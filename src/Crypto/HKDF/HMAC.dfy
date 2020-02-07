include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened Digests
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype {:extern "CipherParameters"} CipherParameters = KeyParameter(key: array<uint8>)

  class {:extern "HMac"} HMac {

    const algorithm: KEY_DERIVATION_ALGORITHM
    ghost var initialized: Option<seq<uint8>>

    // InputSoFar represents the accumulated input as Update calls are made. It is cleared by Reset and DoFinal, though
    // DoFinal additionally outputs the hash of the accumulated input.
    ghost var InputSoFar: seq<uint8>

    constructor {:extern} (algorithm: KEY_DERIVATION_ALGORITHM)
      ensures this.algorithm == algorithm

    function method {:extern "GetMacSize"} getMacSize(): int32
      ensures getMacSize() == HashLength(algorithm)

    predicate {:axiom} validKey(key: seq<uint8>)

    method {:extern "Init"} init(params: CipherParameters)
      // The documentation says it can throw "InvalidKeyException - if the given key is inappropriate for
      // initializing this MAC", which I have interpreted to mean the following precondition:
      //requires key.algorithm == algorithm
      requires params.KeyParameter?
      modifies this
      ensures
        var key := match params case KeyParameter(key) => key;
        match initialized { case Some(k) => validKey(k) && key[..] == k case None => false }
      ensures InputSoFar == []

    method {:extern "Reset"} reset()
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []

    method {:extern "Update"} updateSingle(input: uint8)
      requires initialized.Some?
      modifies this
      ensures unchanged(`initialized)
      ensures InputSoFar == old(InputSoFar) + [input]

    method {:extern "BlockUpdate"} update(input: array<uint8>, inOff: int32, len: int32)
      requires initialized.Some?
      requires inOff >= 0
      requires len >= 0
      requires input.Length < 0x8000_0000
      requires inOff as int + len as int <= input.Length
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff..inOff+len]

    method {:extern "DoFinal"} doFinal(output: array<uint8>, outOff: int32) returns (retVal: int32)
      requires initialized.Some?
      requires outOff >= 0
      requires outOff as int + getMacSize() as int <= output.Length
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize() as int
      requires output.Length < 0x8000_0000
      modifies `InputSoFar, output
      ensures output[..] == old(output[..outOff]) + old(Hash(algorithm, initialized.get, InputSoFar)) + old(output[outOff + getMacSize()..])
      ensures output.Length == old(output.Length)
      ensures InputSoFar == []

    method updateAll(input: array<uint8>)
      requires initialized.Some?
      requires input.Length < 0x8000_0000
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[..]
    {
      update(input, 0, input.Length as int32);
    }
  }
}
