package Signature;

import org.bouncycastle.asn1.ASN1Encodable;
import org.bouncycastle.asn1.ASN1Integer;
import org.bouncycastle.asn1.ASN1Sequence;
import org.bouncycastle.asn1.DERSequence;

import java.io.IOException;
import java.security.Signature;
import java.security.SignatureException;
import java.security.interfaces.ECPrivateKey;

/** Helper methods for calculating a digital signature. */
class SignUtils {

    // This is not in our spec:
    // The ESDK wants a deterministic message size,
    // including the signature in the footer.
    // This "feature" facilitates uploading to S3,
    // and use cases where "disk space" must be pre-allocated before
    // receiving a data stream.
    // Original Author: Bryan Donlan
    static byte[] generateEcdsaFixedLengthSignature(
            final byte[] digest,
            final Signature signatureCipher,
            final ECPrivateKey ecKey,
            final short expectedLength
    ) throws SignatureException {
        byte[] signatureBytes;
        // Unfortunately, we need deterministic lengths while
        // some signatures lengths are non-deterministic.
        // So, we retry until we get the right length :-(
        do {
            signatureCipher.update(digest);
            signatureBytes = signatureCipher.sign();
            if (signatureBytes.length != expectedLength) {
                // Most of the time, a signature of the wrong length can be fixed
                // by negating s in the signature relative to the group order.
                ASN1Sequence seq = ASN1Sequence.getInstance(signatureBytes);
                ASN1Integer r = (ASN1Integer) seq.getObjectAt(0);
                ASN1Integer s = (ASN1Integer) seq.getObjectAt(1);
                s = new ASN1Integer(ecKey.getParams().getOrder().subtract(s.getPositiveValue()));
                seq = new DERSequence(new ASN1Encodable[] {r, s});
                try {
                    signatureBytes = seq.getEncoded();
                } catch (IOException ex) {
                    throw new SignatureException(ex);
                }
            }
        } while (signatureBytes.length != expectedLength);
        return signatureBytes;
    }
}
