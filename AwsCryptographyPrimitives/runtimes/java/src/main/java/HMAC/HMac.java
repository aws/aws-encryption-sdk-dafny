package HMAC;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import org.bouncycastle.util.Bytes;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;

import javax.crypto.Mac;
import javax.crypto.ShortBufferException;
import javax.crypto.spec.SecretKeySpec;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.util.Collections;

public class HMac extends _ExternBase_HMac {

  private String algorithm;
  private Mac hmac;

  public static Result<HMAC.HMac, Error> Build(DigestAlgorithm digest)
  {
    try {
      final HMac output = new HMac(digest);
      return Result.create_Success(output);
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

  public HMac(DigestAlgorithm digest) throws NoSuchAlgorithmException
  {

    if (digest.is_SHA__1()) {
      algorithm = "HmacSHA1";
    } else if (digest.is_SHA__256()) {
      algorithm = "HmacSHA256";
    } else if (digest.is_SHA__384()) {
      algorithm = "HmacSHA384";
    } else if (digest.is_SHA__512()) {
      algorithm = "HmacSHA512";
    } else {
      throw new NoSuchAlgorithmException();
    }

    hmac = Mac.getInstance(algorithm);
  }

  public void Init(DafnySequence<? extends Byte> key)  {
    final byte[] keyBytes = (byte[]) Array.unwrap(key.toArray());
    try {
      final SecretKeySpec secretKey = new SecretKeySpec(keyBytes, algorithm);
      hmac.init(secretKey);
    } catch (InvalidKeyException e) {
      // TODO determine that this really is safe
      // This error appears to be thrown if the key is empty
      // A requires on the Dafny side makes sure this is never called that way
    }
  }

  public void BlockUpdate(DafnySequence<? extends Byte> input) {
    final byte[] inputBytes = (byte[]) Array.unwrap(input.toArray());
    hmac.update(inputBytes);
  }

  public DafnySequence<? extends Byte> GetResult() {
    final byte[] digest = hmac.doFinal();
    return DafnySequence.fromBytes(digest);
  }
}
