package HMAC;

import software.amazon.cryptography.primitives.internaldafny.types.Error;
import StandardLibrary_mUInt_Compile.uint8;
import Wrappers_Compile.Result;
import dafny.DafnySequence;

import java.security.NoSuchAlgorithmException;

public class __default {

  public static Result<DafnySequence<? extends Byte>, Error> Digest(
    software.amazon.cryptography.primitives.internaldafny.types.HMacInput input
  )
  {
    Result<HMac, Error> maybeHMac = HMac.Build(input._digestAlgorithm);
    if (maybeHMac.is_Failure()) {
      return Result.create_Failure(maybeHMac.dtor_error());
    }
    final HMac hmac = maybeHMac.Extract(HMac._typeDescriptor(), Error._typeDescriptor());
    hmac.Init(input._key);
    hmac.BlockUpdate(input._message);
    final DafnySequence<? extends Byte> output = hmac.GetResult();
    return Result.create_Success(output);
  }

}
