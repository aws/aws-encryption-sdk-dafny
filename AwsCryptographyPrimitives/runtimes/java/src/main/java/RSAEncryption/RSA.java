package RSAEncryption;

import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Dafny.Aws.Cryptography.Primitives.Types.RSAPaddingMode;
import Random_Compile.ExternRandom;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import dafny.Tuple2;
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
import org.bouncycastle.crypto.util.PrivateKeyFactory;
import org.bouncycastle.crypto.util.PrivateKeyInfoFactory;
import org.bouncycastle.crypto.util.PublicKeyFactory;
import org.bouncycastle.crypto.util.SubjectPublicKeyInfoFactory;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

import java.io.IOException;
import java.math.BigInteger;
import java.security.SecureRandom;

public class RSA {
    private static int RSA_KEY_STRENGTH_MAX = 4096;
    private static int RSA_PUBLIC_EXPONENT = 65537;
    private static int RSA_CERTAINTY = 256;
    private static String RSA_ERROR_MSG = String.format(
            "AWS Crypto will not generate an RSA Key with Strength greater than %s", RSA_KEY_STRENGTH_MAX);

    public static Tuple2<DafnySequence<? extends Byte>, DafnySequence<? extends Byte>> GenerateKeyPairExtern(int strength) {
        try {
            if (strength > RSA_KEY_STRENGTH_MAX) {
                throw new RuntimeException(RSA_ERROR_MSG);
            }
            RSAKeyPairGenerator keygen = new RSAKeyPairGenerator();
            final SecureRandom secureRandom = ExternRandom.getSecureRandom();
            KeyGenerationParameters keyGenerationParameters = new RSAKeyGenerationParameters(
                    BigInteger.valueOf(RSA_PUBLIC_EXPONENT), secureRandom, strength, RSA_CERTAINTY
            );
            keygen.init(keyGenerationParameters);
            AsymmetricCipherKeyPair keyPair = keygen.generateKeyPair();

            return Tuple2.create(
                    DafnySequence.fromBytes(GetPemBytes(keyPair.getPublic())),
                    DafnySequence.fromBytes(GetPemBytes(keyPair.getPrivate()))
            );
        } catch (Exception e) {
            throw new RuntimeException("Unable to create RSA Key Pair");
        }
    }

    private static byte[] GetPemBytes(AsymmetricKeyParameter keyParameter) throws IOException {
        if (keyParameter.isPrivate()) {
            PrivateKeyInfo privateKey = PrivateKeyInfoFactory.createPrivateKeyInfo(keyParameter);
            return privateKey.getEncoded();
        } else {
            SubjectPublicKeyInfo publicKey = SubjectPublicKeyInfoFactory.createSubjectPublicKeyInfo(keyParameter);
            return publicKey.getEncoded();
        }
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
            byte[] ciphertext = (byte[]) Array.unwrap(dtor_cipherText.toArray());

            AsymmetricBlockCipher engine = GetEngineForPadding(dtor_padding);
            AsymmetricKeyParameter keyParameter = PrivateKeyFactory.createKey(privateKey);
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
            AsymmetricBlockCipher engine = GetEngineForPadding(dtor_padding);
            byte[] publicKey = (byte[]) Array.unwrap(dtor_publicKey.toArray());
            AsymmetricKeyParameter publicKeyParam = PublicKeyFactory.createKey(publicKey);
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
