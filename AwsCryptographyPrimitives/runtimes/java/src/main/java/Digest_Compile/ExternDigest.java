package Digest_Compile;

import software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.Error;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

public class ExternDigest {
  public static class __default {

    public static Result<DafnySequence<? extends Byte>, Error> Digest(
        DigestAlgorithm digestAlgorithm,
        DafnySequence<? extends Byte> dtor_message
    ) {
      final Result<byte[], Error> maybeDigest = internalDigest(digestAlgorithm, dtor_message);
      if (maybeDigest.is_Failure()) {
        return Result.create_Failure(maybeDigest.dtor_error());
      }
      return Result.create_Success(DafnySequence.fromBytes(
              maybeDigest.dtor_value()));
    }

    public static Result<byte[], Error> internalDigest(
            DigestAlgorithm digestAlgorithm,
            DafnySequence<? extends Byte> dtor_message
    ) {
      try {
        final MessageDigest hash = getHash(digestAlgorithm);
        final byte[] messageBytes = (byte[]) Array.unwrap(dtor_message.toArray());
        hash.update(messageBytes);
        final byte[] digest = hash.digest();
        return Result.create_Success(digest);
      } catch ( NoSuchAlgorithmException ex) {
        final Error err = ToDafny.Error(
                AwsCryptographicPrimitivesError
                        .builder()
                        .message("Requested digest Algorithm is not supported.")
                        .cause(ex)
                        .build());
        return Result.create_Failure(err);
      }
    }

    private static MessageDigest getHash(DigestAlgorithm digestAlgorithm) throws NoSuchAlgorithmException {
      if (digestAlgorithm.is_SHA__256()) {
        return MessageDigest.getInstance("SHA-256");
      } else if (digestAlgorithm.is_SHA__384()) {
        return MessageDigest.getInstance("SHA-384");
      } else if (digestAlgorithm.is_SHA__512()) {
        return MessageDigest.getInstance("SHA-512");
      } else {
        throw new NoSuchAlgorithmException();
      }
    }
  }
}
