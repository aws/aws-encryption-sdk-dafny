package RSAEncryption;

import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Dafny.Aws.Cryptography.Primitives.Types.RSAPaddingMode;
import Random_Compile.ExternRandom;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import dafny.Tuple2;
import dafny.TypeDescriptor;
import org.bouncycastle.asn1.pkcs.PrivateKeyInfo;
import org.bouncycastle.asn1.x509.SubjectPublicKeyInfo;
import org.bouncycastle.crypto.AsymmetricBlockCipher;
import org.bouncycastle.crypto.AsymmetricCipherKeyPair;
import org.bouncycastle.crypto.KeyGenerationParameters;
import org.bouncycastle.crypto.digests.SHA1Digest;
import org.bouncycastle.crypto.digests.SHA256Digest;
import org.bouncycastle.crypto.digests.SHA384Digest;
import org.bouncycastle.crypto.digests.SHA512Digest;
import org.bouncycastle.crypto.encodings.OAEPEncoding;
import org.bouncycastle.crypto.encodings.PKCS1Encoding;
import org.bouncycastle.crypto.engines.RSABlindedEngine;
import org.bouncycastle.crypto.generators.RSAKeyPairGenerator;
import org.bouncycastle.crypto.params.AsymmetricKeyParameter;
import org.bouncycastle.crypto.params.RSAKeyGenerationParameters;
import org.bouncycastle.crypto.params.RSAKeyParameters;
import org.bouncycastle.crypto.util.PrivateKeyFactory;
import org.bouncycastle.crypto.util.PrivateKeyInfoFactory;
import org.bouncycastle.crypto.util.PublicKeyFactory;
import org.bouncycastle.crypto.util.SubjectPublicKeyInfoFactory;
import org.bouncycastle.util.io.pem.PemWriter;
import org.bouncycastle.util.io.pem.PemReader;
import org.bouncycastle.util.io.pem.PemObject;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

import java.security.SecureRandom;
import java.security.spec.X509EncodedKeySpec;
import java.nio.charset.StandardCharsets;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringWriter;
import java.nio.ByteBuffer;
import java.math.BigInteger;

import static software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence;

public class RSA {
    private static int RSA_KEY_LEN_MAX = 4096;
    private static int RSA_PUBLIC_EXPONENT = 65537;
    private static int RSA_CERTAINTY = 256;
    private static String RSA_ERROR_MSG = String.format(
            "AWS Crypto will not generate an RSA Key with length greater than %s", RSA_KEY_LEN_MAX);

    public static Tuple2<DafnySequence<? extends Byte>, DafnySequence<? extends Byte>> GenerateKeyPairExtern(int lengthBits) {
        try {
            if (lengthBits > RSA_KEY_LEN_MAX) {
                throw new RuntimeException(RSA_ERROR_MSG);
            }
            RSAKeyPairGenerator keygen = new RSAKeyPairGenerator();
            final SecureRandom secureRandom = ExternRandom.getSecureRandom();
            KeyGenerationParameters keyGenerationParameters = new RSAKeyGenerationParameters(
                    BigInteger.valueOf(RSA_PUBLIC_EXPONENT), secureRandom, lengthBits, RSA_CERTAINTY
            );
            keygen.init(keyGenerationParameters);
            AsymmetricCipherKeyPair keyPair = keygen.generateKeyPair();

            return Tuple2.create(
                    GetPemBytes(keyPair.getPublic()),
                    GetPemBytes(keyPair.getPrivate())
            );
        } catch (Exception e) {
            throw new RuntimeException("Unable to create RSA Key Pair");
        }
    }

    public static Result<Integer, Error>  GetRSAKeyModulusLengthExtern(DafnySequence<? extends Byte> dtor_publicKey) {
        try {
            byte[] pemBytes = (byte[]) Array.unwrap(dtor_publicKey.toArray());
            RSAKeyParameters keyParams = ParsePublicRsaPemBytes(pemBytes);
            return Result.create_Success(keyParams.getModulus().bitLength());
        } catch (Exception e) {
            return Result.create_Failure(ToDafny.Error(
                OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build())
            );
        }
    }

    // GetPemBytes represents a helper method that takes an AsymmetricKeyParameter and returns the corresponding
    // private key or public key, PEM encoded, as UTF-8 bytes.
    // Public keys are DER-encoded X.509 SubjectPublicKeyInfo, as specified in RFC 5280.
    // Private keys are DER-encoded PKCS8 PrivateKeyInfo, as specified in RFC 5958.
    private static DafnySequence<? extends Byte> GetPemBytes(AsymmetricKeyParameter keyParameter) throws IOException {
        if (keyParameter.isPrivate()) {
            PrivateKeyInfo privateKey = PrivateKeyInfoFactory.createPrivateKeyInfo(keyParameter);
            StringWriter stringWriter = new StringWriter();
            PemWriter pemWriter = new PemWriter(stringWriter);
            pemWriter.writeObject(new PemObject("PRIVATE KEY", privateKey.getEncoded()));
            pemWriter.close();
            ByteBuffer outBuffer = StandardCharsets.UTF_8.encode(stringWriter.toString());
            return ByteSequence(outBuffer, 0, outBuffer.limit());
        } else {
            SubjectPublicKeyInfo publicKey = SubjectPublicKeyInfoFactory.createSubjectPublicKeyInfo(keyParameter);
            StringWriter stringWriter = new StringWriter();
            PemWriter pemWriter = new PemWriter(stringWriter);
            pemWriter.writeObject(new PemObject("PUBLIC KEY", publicKey.getEncoded()));
            pemWriter.close();
            ByteBuffer outBuffer = StandardCharsets.UTF_8.encode(stringWriter.toString());
            return ByteSequence(outBuffer, 0, outBuffer.limit());
        }
    }

    // Parses UTF8-encoded, PEM-encoded RSA Public keys.
    private static RSAKeyParameters ParsePublicRsaPemBytes(byte[] pem) throws IOException {
        PemReader pemReader = new PemReader(new InputStreamReader(new ByteArrayInputStream(pem)));
        PemObject pemObject = pemReader.readPemObject();
        byte[] content = pemObject.getContent();
        RSAKeyParameters publicKeyParams = (RSAKeyParameters) PublicKeyFactory.createKey(content);
        return publicKeyParams;
    }

    // Parses UTF8-encoded, PEM-encoded RSA Private keys.
    private static RSAKeyParameters ParsePrivateRsaPemBytes(byte[] pem) throws IOException {
        PemReader pemReader = new PemReader(new InputStreamReader(new ByteArrayInputStream(pem)));
        PemObject pemObject = pemReader.readPemObject();
        byte[] content = pemObject.getContent();
        RSAKeyParameters privateKeyParams = (RSAKeyParameters) PrivateKeyFactory.createKey(content);
        return privateKeyParams;
    }


    // GetEngineForPadding represents a helper method that takes in a RSAPaddingMode and returns a
    // AsymmetricBlockCipher for the RsaBlindedEngine that uses the appropriate digest or throws a
    // RSAUnsupportedPaddingSchemeException if no valid padding exists
    private static AsymmetricBlockCipher GetEngineForPadding(RSAPaddingMode paddingMode) {
        if (paddingMode.is_OAEP__SHA1()) {
           return new OAEPEncoding(new RSABlindedEngine(), new SHA1Digest());
        } else if (paddingMode.is_OAEP__SHA256()) {
            return new OAEPEncoding(new RSABlindedEngine(), new SHA256Digest());
        } else if (paddingMode.is_OAEP__SHA384()) {
            return new OAEPEncoding(new RSABlindedEngine(), new SHA384Digest());
        } else if (paddingMode.is_OAEP__SHA512()) {
            return new OAEPEncoding(new RSABlindedEngine(), new SHA512Digest());
        } else if (paddingMode.is_PKCS1()) {
            return new PKCS1Encoding(new RSABlindedEngine());
        } else {
            throw new RuntimeException(String.format("Invalid RSA Padding Scheme %s", paddingMode));
        }
    }

    public static Result<DafnySequence<? extends Byte>, Error> DecryptExtern(
            RSAPaddingMode dtor_padding,
            DafnySequence<? extends Byte> dtor_privateKey,
            DafnySequence<? extends Byte> dtor_cipherText
    ) {
        try {
            byte[] privateKey = (byte[]) Array.unwrap(dtor_privateKey.toArray());
            RSAKeyParameters keyParameter = ParsePrivateRsaPemBytes(privateKey);

            byte[] ciphertext = (byte[]) Array.unwrap(dtor_cipherText.toArray());

            AsymmetricBlockCipher engine = GetEngineForPadding(dtor_padding);
            engine.init(false, keyParameter);

            return Result.create_Success(
                    DafnySequence.fromBytes(
                            engine.processBlock(
                                    ciphertext,
                                    0,
                                    ciphertext.length
                            )
                    )
            );
        } catch (Exception e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build())
            );
        }
    }

    public static Result<DafnySequence<? extends Byte>, Error> EncryptExtern(
            RSAPaddingMode dtor_padding,
            DafnySequence<? extends Byte> dtor_publicKey,
            DafnySequence<? extends Byte> dtor_plaintext
    ) {
        try {

            byte[] publicKey = (byte[]) Array.unwrap(dtor_publicKey.toArray());
            RSAKeyParameters publicKeyParam = ParsePublicRsaPemBytes(publicKey);

            AsymmetricBlockCipher engine = GetEngineForPadding(dtor_padding);
            engine.init(true, publicKeyParam);

            return Result.create_Success(
                    DafnySequence.fromBytes(
                            engine.processBlock(
                                    (byte[]) Array.unwrap(dtor_plaintext.toArray()),
                                    0,
                                    dtor_plaintext.toArray().length())
                    )
            );
        } catch (Exception e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build())
            );
        }
    }
}
