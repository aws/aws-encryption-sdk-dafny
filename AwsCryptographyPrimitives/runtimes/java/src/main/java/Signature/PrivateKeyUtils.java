package Signature;

import java.math.BigInteger;
import java.security.KeyFactory;
import java.security.NoSuchAlgorithmException;
import java.security.interfaces.ECPrivateKey;
import java.security.spec.ECParameterSpec;
import java.security.spec.ECPrivateKeySpec;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.InvalidParameterSpecException;

import software.amazon.cryptography.primitives.internaldafny.types.Error;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

/** Helper methods for encoding and decoding Elliptic Curve private keys. */
class PrivateKeyUtils {
    // Based on our ESDK-Net implementation,
    // ../../../../../net/Extern/Signature.cs#L46
    // we convert the BigInteger to Byte Array with the sign.
    // Bouncy Castle NET's Source code and documents are not clear if that
    // is a big-endian Two's Complement or some other representation.
    // Here, we are using Java's BigInteger to get
    // the big-endian Two's Complement with the sign.
    // However, the private key is ephemeral;
    // it will always be generated and used in the same runtime.
    // As such, we do not have to ensure that our different runtimes
    // encode the private key identically.
    static byte[] encodePrivateKey(final ECPrivateKey privateKey) {
        return privateKey.getS().toByteArray();
    }

    static Result<ECPrivateKey, Error> decodePrivateKey(
            SignatureAlgorithm algorithm,
            DafnySequence<? extends Byte> dtor_signingKey
    ) {
        final ECPrivateKey privateKey;
        try {
            final ECParameterSpec ecParameterSpec = SignatureAlgorithm.ecParameterSpec(algorithm);
            final byte[] keyAsBytes = (byte[]) Array.unwrap(dtor_signingKey.toArray());
            final ECPrivateKeySpec privateKeySpec = new ECPrivateKeySpec(
                    new BigInteger(keyAsBytes), ecParameterSpec);
            // The following should result in
            // sun.security.ec.ECKeyFactory.implGeneratePrivate
            // or something equivalent.
            // "generatePrivate" is a misnomer;
            // it's really a deterministic factory method.
            privateKey = (ECPrivateKey) KeyFactory.getInstance(ECDSA.ELLIPTIC_CURVE_ALGORITHM)
                                                .generatePrivate(privateKeySpec);
        } catch (NoSuchAlgorithmException | InvalidParameterSpecException | InvalidKeySpecException e) {
            // The private key will always be generated in this runtime (Java);
            // these exceptions SHOULD BE impossible.
            return Result.create_Failure(ToDafny.Error(
                    OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build()));
        }
        return Result.create_Success(privateKey);
    }
}
