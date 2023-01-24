package Signature;

import java.security.AlgorithmParameters;
import java.security.NoSuchAlgorithmException;
import java.security.spec.ECGenParameterSpec;
import java.security.spec.ECParameterSpec;
import java.security.spec.InvalidParameterSpecException;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.ECDSASignatureAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;

import static Signature.ECDSA.SEC_P256;
import static Signature.ECDSA.SEC_P384;
import static Signature.ECDSA.SEC_PRIME_FIELD_PREFIX;

public enum SignatureAlgorithm {
    P256(SEC_PRIME_FIELD_PREFIX+SEC_P256, DigestAlgorithm.create_SHA__256(), "NONEwithECDSA", (short) 71),
    P384(SEC_PRIME_FIELD_PREFIX+SEC_P384, DigestAlgorithm.create_SHA__384(), "NONEwithECDSA", (short) 103);

    public final String curve;
    public final DigestAlgorithm messageDigestAlgorithm;
    public final String rawSignatureAlgorithm;
    public final short expectedSignatureLength;
    
    SignatureAlgorithm(
            final String curve,
            final DigestAlgorithm messageDigestAlgorithm,
            final String rawSignatureAlgorithm,
            final short expectedSignatureLength
    ) {
        this.curve = curve;
        this.messageDigestAlgorithm = messageDigestAlgorithm;
        this.rawSignatureAlgorithm = rawSignatureAlgorithm;
        this.expectedSignatureLength = expectedSignatureLength;
    }

    static Result<SignatureAlgorithm, Error> signatureAlgorithm(ECDSASignatureAlgorithm dtor_signatureAlgorithm) {
        final SignatureAlgorithm signatureAlgorithm;
        //= aws-encryption-sdk-specification/framework/transitive-requirements.md#ecdsa
        //# If specified to use ECDSA, the AWS Encryption SDK MUST use ECDSA with the following specifics:
        //# - The elliptic curve is specified by the algorithm suite.
        //#   The specific curves are defined in
        //#   [Digital Signature Standard (DSS) (FIPS PUB 186-4)](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf).
        if (dtor_signatureAlgorithm.is_ECDSA__P256()) {
            signatureAlgorithm = P256;
        } else if (dtor_signatureAlgorithm.is_ECDSA__P384()) {
            signatureAlgorithm = P384;
        } else {
            return Result.create_Failure(ToDafny.Error(
                    AwsCryptographicPrimitivesError.builder().message(
                                    String.format("Requested Curve is not supported. Requested %s.",
                                            dtor_signatureAlgorithm))
                            .build()));
        }
        return Result.create_Success(signatureAlgorithm);
    }

    static ECParameterSpec ecParameterSpec(
            SignatureAlgorithm algorithm
    ) throws NoSuchAlgorithmException, InvalidParameterSpecException {
        final ECGenParameterSpec genParameterSpec =
                new ECGenParameterSpec(algorithm.curve);
        final AlgorithmParameters parameters =
                AlgorithmParameters.getInstance(ECDSA.ELLIPTIC_CURVE_ALGORITHM);
        parameters.init(genParameterSpec);
        return parameters.getParameterSpec(ECParameterSpec.class);
    }

}
