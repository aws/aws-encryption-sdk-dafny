package Signature;

import Utils.Util;
import dafny.DafnySequence;
import dafny.Tuple2;
import dafny.UByte;
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

import static Utils.Util.bytesToUByteSequence;
import static Utils.Util.uByteSequenceToBytes;

public class ECDSA {
    public static STL.Option<Tuple2<DafnySequence<UByte>, DafnySequence<UByte>>> KeyGen(ECDSAParams x) {
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
            DafnySequence<UByte> vk = bytesToUByteSequence(pt.getEncoded());
            DafnySequence<UByte> sk = bytesToUByteSequence(((ECPrivateKeyParameters)kp.getPrivate()).getD().toByteArray());
            return new STL.Option_Some<>(new Tuple2<>(vk, sk));
        } catch (RuntimeException e) {
            return new STL.Option_None<>();
        }
    }

    public static boolean Verify(ECDSAParams x, DafnySequence<UByte> vk, DafnySequence<UByte> digest, DafnySequence<UByte> sig) {
        try {
            ECNamedCurveParameterSpec p;
            if (x.is_ECDSA__P384()) {
                p = ECNamedCurveTable.getParameterSpec("secp384r1");
            } else {
                p = ECNamedCurveTable.getParameterSpec("secp256r1");
            }
            ECDomainParameters dp = new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH());
            ECPoint pt = p.getCurve().decodePoint(uByteSequenceToBytes(vk));
            ECPublicKeyParameters vkp = new ECPublicKeyParameters(pt, dp);
            ECDSASigner sign = new ECDSASigner();
            sign.init(false, vkp);
            BigInteger r, s;
            Tuple2<BigInteger, BigInteger> pair = DERDeserialize(uByteSequenceToBytes(sig));
            return sign.verifySignature(uByteSequenceToBytes(digest), pair.dtor__0(), pair.dtor__1());
        } catch (Exception e) {
            return false;
        }
    }

    public static STL.Option<DafnySequence<UByte>> Sign(ECDSAParams x, DafnySequence<UByte> sk, DafnySequence<UByte> digest) {
        try {
            ECNamedCurveParameterSpec p;
            if (x.is_ECDSA__P384()) {
                p = ECNamedCurveTable.getParameterSpec("secp384r1");
            } else {
                p = ECNamedCurveTable.getParameterSpec("secp256r1");
            }
            ECDomainParameters dp = new ECDomainParameters(p.getCurve(), p.getG(), p.getN(), p.getH());
            ECPrivateKeyParameters skp = new ECPrivateKeyParameters(new BigInteger(uByteSequenceToBytes(sk)), dp);
            ECDSASigner sign = new ECDSASigner();
            sign.init(true, skp);
            do {
                BigInteger[] sig = sign.generateSignature(uByteSequenceToBytes(digest));
                byte[] bytes = DERSerialize(sig[0], sig[1]);
                if (bytes.length != x.SignatureLength().intValue()) {
                    // Most of the time, a signature of the wrong length can be fixed
                    // by negating s in the signature relative to the group order.
                    bytes = DERSerialize(sig[0], p.getN().subtract(sig[1]));
                }
                if (bytes.length == x.SignatureLength().intValue()) {
                    // This will meet the method postcondition, which says that a Some? return must
                    // contain a sequence of bytes whose length is x.SignatureLength().
                    return new STL.Option_Some<>(bytesToUByteSequence(bytes));
                }
                // We only get here with low probability, so try again (forever, if we have really bad luck).
            } while (true);
        } catch (RuntimeException e) {
            return new STL.Option_None<>();
        }
    }

    public static DafnySequence<UByte> Digest(ECDSAParams x, DafnySequence<UByte> msg) {
        MessageDigest alg;
        if (x.is_ECDSA__P384()) {
            alg = new JDKMessageDigest.SHA384();
        } else {
            alg = new JDKMessageDigest.SHA256();
        }
        byte[] digest = alg.digest(uByteSequenceToBytes(msg));
        return bytesToUByteSequence(digest);
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
