package Signature;

import java.math.BigInteger;
import java.security.KeyFactory;
import java.security.NoSuchAlgorithmException;
import java.security.PublicKey;
import java.security.interfaces.ECPublicKey;
import java.security.spec.ECFieldFp;
import java.security.spec.ECParameterSpec;
import java.security.spec.ECPoint;
import java.security.spec.ECPublicKeySpec;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.InvalidParameterSpecException;
import java.util.Arrays;
import java.util.Objects;

import Dafny.Aws.Cryptography.Primitives.Types.ECDSASignatureAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;
import software.amazon.cryptography.primitives.model.OpaqueError;

import static Signature.ECDSA.FOUR;
import static Signature.ECDSA.THREE;
import static Signature.ECDSA.TWO;
import static java.math.BigInteger.ONE;
import static java.math.BigInteger.ZERO;

/** Helper methods for encoding and decoding Elliptic Curve public keys. */
class PublicKeyUtils {
    /**
     * @param key The Elliptic Curve public key to
     *            encode and compress as described in SEC-1 v2 section 2.3.3
     * @param dtor_signatureAlgorithm The Elliptic Curve algorithm
     * @return byte[] The encoded and compressed public key
     * @see <a href="http://www.secg.org/sec1-v2.pdf">http://www.secg.org/sec1-v2.pdf</a>
     */
    static byte[] encodeAndCompressPublicKey(PublicKey key, ECDSASignatureAlgorithm dtor_signatureAlgorithm) {
        Objects.requireNonNull(key, "key is required");
        if (!(key instanceof ECPublicKey)) {
            throw new IllegalArgumentException("key must be an instance of ECPublicKey");
        }

        final BigInteger x = ((ECPublicKey) key).getW().getAffineX();
        final BigInteger y = ((ECPublicKey) key).getW().getAffineY();
        final BigInteger compressedY = y.mod(TWO).equals(ZERO) ? TWO : THREE;

        // The Dafny Source FieldSize methods includes the compressed Y-Byte.
        final int xFieldSize = _ExternBase___default.FieldSize(dtor_signatureAlgorithm).intValueExact() - 1;
        final byte[] xBytes = encodeAndCompressPublicKeyX(x, xFieldSize);

        final byte[] compressedKey = new byte[xBytes.length + 1];
        System.arraycopy(xBytes, 0, compressedKey, 1, xBytes.length);
        compressedKey[0] = compressedY.byteValue();
        return compressedKey;
    }

    /**
     * Removes the leading zero sign byte from the byte array representation of a BigInteger (if
     * present) and left pads with zeroes to produce a byte array of the given length.
     *
     * @param bigInteger The BigInteger to convert to a byte array
     * @param length The length of the byte array, must be at least as long as the BigInteger byte
     *     array without the sign byte
     * @return The byte array
     */
    static byte[] encodeAndCompressPublicKeyX(final BigInteger bigInteger, final int length) {
        byte[] rawBytes = bigInteger.toByteArray();
        // If rawBytes is already the correct length, return it.
        if (rawBytes.length == length) {
            return rawBytes;
        }

        // If we're exactly one byte too large, but we have a leading zero byte, remove it and return.
        if (rawBytes.length == length + 1 && rawBytes[0] == 0) {
            return Arrays.copyOfRange(rawBytes, 1, rawBytes.length);
        }

        if (rawBytes.length > length) {
            throw new IllegalArgumentException(
                    "Length must be at least as long as the BigInteger byte array "
                            + "without the sign byte");
        }

        final byte[] paddedResult = new byte[length];
        System.arraycopy(rawBytes, 0, paddedResult, length - rawBytes.length, rawBytes.length);
        return paddedResult;
    }

    static Result<ECPublicKey, Error> decodePublicKey(
            SignatureAlgorithm algorithm,
            DafnySequence<? extends Byte> dtor_verificationKey
    ) {
        final ECPublicKey publicKey;
        try {
            final ECParameterSpec ecParameterSpec = SignatureAlgorithm.ecParameterSpec(algorithm);
            final byte[] keyAsBytes = (byte[]) Array.unwrap(dtor_verificationKey.toArray());
            final ECPublicKeySpec publicKeySpec = new ECPublicKeySpec(
                    byteArrayToECPoint(keyAsBytes, ecParameterSpec), ecParameterSpec);
            // The following should result in
            // sun.security.ec.ECKeyFactory.implGeneratePublic
            // or something equivalent.
            // "generatePublic" is a misnomer;
            // it's really a deterministic factory method.
            publicKey = (ECPublicKey) KeyFactory.getInstance(ECDSA.ELLIPTIC_CURVE_ALGORITHM)
                                                .generatePublic(publicKeySpec);
        } catch (ECDecodingException ex) {
            return Result.create_Failure(ToDafny.Error(
                    AwsCryptographicPrimitivesError.builder()
                            .message(String.format(
                                    "Could not decode Elliptic Curve point due to: %s.",
                                    ex.getMessage()))
                            .cause(ex)
                            .build()));
        } catch ( NoSuchAlgorithmException | InvalidKeySpecException | InvalidParameterSpecException e) {
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build()));
        }
        return Result.create_Success(publicKey);
    }

    /**
     * Decodes a compressed elliptic curve point as described in SEC-1 v2 section 2.3.4.<p>
     * Original Author: Wesley Rosenblum
     *
     * @param keyAsBytes The encoded and compressed Elliptic Curve public key.
     * @param ecParameterSpec Elliptic Curve parameter spec describing the curve.
     * @return The Elliptic Curve point.
     * @see <a href="http://www.secg.org/sec1-v2.pdf">http://www.secg.org/sec1-v2.pdf</a>
     */
    static ECPoint byteArrayToECPoint(
            final byte[] keyAsBytes,
            final ECParameterSpec ecParameterSpec
    ) throws ECDecodingException {
        final BigInteger x = new BigInteger(1, Arrays.copyOfRange(keyAsBytes, 1, keyAsBytes.length));

        final byte compressedY = keyAsBytes[0];
        final BigInteger yOrder;

        if (compressedY == TWO.byteValue()) {
            yOrder = ZERO;
        } else if (compressedY == THREE.byteValue()) {
            yOrder = ONE;
        } else {
            throw new ECDecodingException("Compressed y value was invalid");
        }

        final BigInteger p = ((ECFieldFp) ecParameterSpec.getCurve().getField()).getP();
        final BigInteger a = ecParameterSpec.getCurve().getA();
        final BigInteger b = ecParameterSpec.getCurve().getB();

        // alpha must be equal to y^2, this is validated below
        final BigInteger alpha = x.modPow(THREE, p).add(a.multiply(x).mod(p)).add(b).mod(p);

        final BigInteger beta;
        if (p.mod(FOUR).equals(THREE)) {
            beta = alpha.modPow(p.add(ONE).divide(FOUR), p);
        } else {
            throw new ECDecodingException("Curve not supported at this time");
        }

        //noinspection SuspiciousNameCombination
        final BigInteger y = beta.mod(TWO).equals(yOrder) ? beta : p.subtract(beta);

        // Validate that Y is a root of Y^2 to prevent invalid point attacks
        if (!alpha.equals(y.modPow(TWO, p))) {
            throw new ECDecodingException("Y was invalid");
        }
        return new ECPoint(x, y);
    }

    static class ECDecodingException extends RuntimeException {
        ECDecodingException(String message) {
            super(message);
        }
    }

}
