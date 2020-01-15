package RSAEncryption;

import Utils.BouncyCastleUtils;
import dafny.DafnySequence;
import dafny.Tuple2;
import org.bouncycastle.openssl.PEMReader;
import org.bouncycastle.openssl.PEMWriter;

import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.NoSuchPaddingException;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.StringWriter;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.*;
import java.security.spec.RSAKeyGenParameterSpec;

import static Utils.Util.*;

public class RSA {
    public static Tuple2<byte[], byte[]> get_pem(KeyPair kp) {
        try {
            byte[] pk;
            {
                StringWriter stringWriter = new StringWriter();
                PEMWriter pemWriter = new PEMWriter(stringWriter);
                pemWriter.writeObject(kp.getPublic());
                pemWriter.flush();
                pk = stringWriter.toString().getBytes(StandardCharsets.UTF_8);
            }

            byte[] sk;
            {
                StringWriter stringWriter = new StringWriter();
                PEMWriter pemWriter = new PEMWriter(stringWriter);
                pemWriter.writeObject(kp.getPrivate());
                pemWriter.flush();
                sk = stringWriter.toString().getBytes(StandardCharsets.UTF_8);
            }

            return new Tuple2<>(pk, sk);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static final BigInteger RSA_PUBLIC_EXPONENT = BigInteger.valueOf(65537);
    // XXX This parameter is passed using the Bouncy Castle API in the C# implementation,
    // but there doesn't appear to be a way to pass it using JCE
    @SuppressWarnings("unused")
    public static final int RSA_CERTAINTY = 256;

    public static Tuple2<DafnySequence<Byte>, DafnySequence<Byte>> GenerateKeyPairExtern(int bits, PaddingMode padding) {
        KeyPairGenerator gen;
        try {
            gen = KeyPairGenerator.getInstance("RSA", BouncyCastleUtils.getProvider());
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
        try {
            gen.initialize(new RSAKeyGenParameterSpec(bits, RSA_PUBLIC_EXPONENT));
        } catch (InvalidAlgorithmParameterException e) {
            throw new RuntimeException(e);
        }

        KeyPair kp = gen.generateKeyPair();
        Tuple2<byte[], byte[]> pair = get_pem(kp);
        return new Tuple2<>(DafnySequence.fromBytes(pair.dtor__0()), DafnySequence.fromBytes(pair.dtor__1()));
    }

    public static STL.Result<DafnySequence<Byte>> EncryptExtern(PaddingMode padding, DafnySequence<Byte> ek, DafnySequence<Byte> msg) {
        try {
            java.security.PublicKey pub;
            PEMReader pemReader = new PEMReader(new StringReader(byteSequenceToString(ek)));
            Object pemObject = pemReader.readObject();
            pub = ((java.security.PublicKey)pemObject);

            Cipher engine = createEngine(padding);

            engine.init(Cipher.ENCRYPT_MODE, pub);
            return new STL.Result_Success<>(DafnySequence.fromBytes(engine.doFinal(DafnySequence.toByteArray(msg))));
        }
        catch (IOException | InvalidKeyException | IllegalBlockSizeException | BadPaddingException e){
            return new STL.Result_Failure<>(DafnySequence.asString("rsa encrypt error"));
        }

    }

    public static STL.Result<DafnySequence<Byte>> DecryptExtern(PaddingMode padding, DafnySequence<Byte> dk, DafnySequence<Byte> ctx) {
        try {
            KeyPair keyPair;

            Cipher engine = createEngine(padding);

            Reader txtreader = new StringReader(byteSequenceToString(dk));
            keyPair = (KeyPair) new PEMReader(txtreader).readObject();
            engine.init(Cipher.DECRYPT_MODE, keyPair.getPrivate());
            return new STL.Result_Success<>(DafnySequence.fromBytes(engine.doFinal(DafnySequence.toByteArray(ctx))));
        }
        catch (IOException | InvalidKeyException | IllegalBlockSizeException | BadPaddingException e){
            return new STL.Result_Failure<>(DafnySequence.asString("rsa decrypt error"));
        }
    }

    public static Cipher createEngine(PaddingMode padding) {
        String alg;

        if (padding.is_PKCS1()) {
            alg = "RSA/ECB/PKCS1Padding";
        } else if (padding.is_OAEP__SHA1()) {
            alg = "RSA/ECB/OAEPWithSHA-1AndMGF1Padding";
        } else { // padding.is_OAEP__SHA256
            alg = "RSA/ECB/OAEPWithSHA-256AndMGF1Padding";
        }

        try {
            return Cipher.getInstance(alg, BouncyCastleUtils.getProvider());
        } catch (NoSuchAlgorithmException | NoSuchPaddingException e) {
            throw new RuntimeException(e);
        }
    }
}
