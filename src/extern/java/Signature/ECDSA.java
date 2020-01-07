package Signature;

import dafny.DafnySequence;
import dafny.Tuple2;
import org.bouncycastle.asn1.*;
import org.bouncycastle.crypto.AsymmetricCipherKeyPair;
import org.bouncycastle.crypto.generators.ECKeyPairGenerator;
import org.bouncycastle.crypto.params.ECDomainParameters;
import org.bouncycastle.crypto.params.ECKeyGenerationParameters;
import org.bouncycastle.crypto.params.ECPrivateKeyParameters;
import org.bouncycastle.crypto.params.ECPublicKeyParameters;
import org.bouncycastle.crypto.signers.ECDSASigner;
import org.bouncycastle.jce.ECNamedCurveTable;
import org.bouncycastle.jce.provider.JDKMessageDigest;
import org.bouncycastle.jce.spec.ECNamedCurveParameterSpec;
import org.bouncycastle.math.ec.ECPoint;

import java.io.IOException;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.SecureRandom;

public class ECDSA {
    public static STL.Option<Tuple2<DafnySequence<Byte>, DafnySequence<Byte>>> KeyGen(ECDSAParams x) {
        try {
            ECKeyPairGenerator g = new ECKeyPairGenerator();
            SecureRandom rng = new SecureRandom();
            ECNamedCurveParameterSpec p;
            if (x.is_ECDSA__P384()) {
                p = ECNamedCurveTable.getParameterSpec("secp384r1");
                g.init(new ECKeyGenerationParameters(new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH()), rng));
            } else { // x is ECDSA__P256
                p = ECNamedCurveTable.getParameterSpec("secp256r1");
                g.init(new ECKeyGenerationParameters(new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH()), rng));
            }
            AsymmetricCipherKeyPair kp = g.generateKeyPair();
            ECPoint pt = ((ECPublicKeyParameters)kp.getPublic()).getQ();
            DafnySequence<Byte> vk = DafnySequence.fromBytes(pt.getEncoded());
            DafnySequence<Byte> sk = DafnySequence.fromBytes(((ECPrivateKeyParameters) kp.getPrivate()).getD().toByteArray());
            return new STL.Option_Some<>(new Tuple2<>(vk, sk));
        } catch (RuntimeException e) {
            return new STL.Option_None<>();
        }
    }

    public static boolean Verify(ECDSAParams x, DafnySequence<Byte> vk, DafnySequence<Byte> digest, DafnySequence<Byte> sig) {
        try {
            ECNamedCurveParameterSpec p;
            if (x.is_ECDSA__P384()) {
                p = ECNamedCurveTable.getParameterSpec("secp384r1");
            } else {
                p = ECNamedCurveTable.getParameterSpec("secp256r1");
            }
            ECDomainParameters dp = new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH());
            ECPoint pt = p.getCurve().decodePoint(DafnySequence.toByteArray(vk));
            ECPublicKeyParameters vkp = new ECPublicKeyParameters(pt, dp);
            ECDSASigner sign = new ECDSASigner();
            sign.init(false, vkp);
            BigInteger r, s;
            Tuple2<BigInteger, BigInteger> pair = DERDeserialize(DafnySequence.toByteArray(sig));
            return sign.verifySignature(DafnySequence.toByteArray(digest), pair.dtor__0(), pair.dtor__1());
        } catch (Exception e) {
            return false;
        }
    }

    public static STL.Option<DafnySequence<Byte>> Sign(ECDSAParams x, DafnySequence<Byte> sk, DafnySequence<Byte> digest) {
        try {
            ECNamedCurveParameterSpec p;
            if (x.is_ECDSA__P384()) {
                p = ECNamedCurveTable.getParameterSpec("secp384r1");
            } else {
                p = ECNamedCurveTable.getParameterSpec("secp256r1");
            }
            ECDomainParameters dp = new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH());
            ECPrivateKeyParameters skp = new ECPrivateKeyParameters(new BigInteger(DafnySequence.toByteArray(sk)), dp);
            ECDSASigner sign = new ECDSASigner();
            sign.init(true, skp);
            do {
                BigInteger[] sig = sign.generateSignature(DafnySequence.toByteArray(digest));
                byte[] bytes = DERSerialize(sig[0], sig[1]);
                if (bytes.length != x.SignatureLength()) {
                    // Most of the time, a signature of the wrong length can be fixed
                    // by negating s in the signature relative to the group order.
                    bytes = DERSerialize(sig[0], p.getN().subtract(sig[1]));
                }
                if (bytes.length == x.SignatureLength()) {
                    // This will meet the method postcondition, which says that a Some? return must
                    // contain a sequence of bytes whose length is x.SignatureLength().
                    return new STL.Option_Some<>(DafnySequence.fromBytes(bytes));
                }
                // We only get here with low probability, so try again (forever, if we have really bad luck).
            } while (true);
        } catch (RuntimeException e) {
            return new STL.Option_None<>();
        }
    }

    public static DafnySequence<Byte> Digest(ECDSAParams x, DafnySequence<Byte> msg) {
        MessageDigest alg;
        if (x.is_ECDSA__P384()) {
            alg = new JDKMessageDigest.SHA384();
        } else {
            alg = new JDKMessageDigest.SHA256();
        }
        byte[] digest = alg.digest(DafnySequence.toByteArray(msg));
        return DafnySequence.fromBytes(digest);
    }

    private static byte[] DERSerialize(BigInteger r, BigInteger s) {
        DERSequence derSeq = new DERSequence(new ASN1Encodable[] { new DERInteger(r), new DERInteger(s) });
        try {
            return derSeq.getEncoded();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static Tuple2<BigInteger, BigInteger> DERDeserialize(byte[] bytes) {
        ASN1InputStream asn1 = new ASN1InputStream(bytes);
        ASN1Sequence seq;
        try {
            seq = (ASN1Sequence) asn1.readObject();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        DERInteger dr = (DERInteger) seq.getObjectAt(0);
        DERInteger ds = (DERInteger) seq.getObjectAt(1);
        BigInteger r = new BigInteger(dr.toString());
        BigInteger s = new BigInteger(ds.toString());
        return new Tuple2<>(r, s);
    }
}
