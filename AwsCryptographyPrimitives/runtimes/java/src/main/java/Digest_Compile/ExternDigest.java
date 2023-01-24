package Digest_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
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
        DafnySequence<? extends Byte> message
    ) {
      try {
        final MessageDigest hash = getHash(digestAlgorithm);
        final byte[] messageBytes = (byte[]) Array.unwrap(message.toArray());
        hash.update(messageBytes);
        final byte[] digest = hash.digest();
        return Result.create_Success(DafnySequence.fromBytes(digest));
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
      if (digestAlgorithm.is_SHA__1()) {
        return MessageDigest.getInstance("SHA-1");
      } else if (digestAlgorithm.is_SHA__256()) {
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
