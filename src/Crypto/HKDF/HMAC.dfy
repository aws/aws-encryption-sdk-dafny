include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened Digests
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype {:extern "CipherParameters"} CipherParameters = KeyParameter(key: seq<uint8>)

  class {:extern "HMac"} HMac {

    const algorithm: KeyDerivationAlgorithm
    ghost var initialized: Option<seq<uint8>>
    ghost var InputSoFar: seq<uint8>

    constructor {:extern} (algorithm: KeyDerivationAlgorithm)
      requires algorithm != IDENTITY
      ensures this.algorithm == algorithm

    function method {:extern "GetMacSize"} getMacSize(): int32
      requires algorithm != IDENTITY
      ensures getMacSize() == HashLength(algorithm)

    predicate {:axiom} validKey(key: seq<uint8>)

    method {:extern "Init"} init(params: CipherParameters)
      // The documentation says it can throw "InvalidKeyException - if the given key is inappropriate for
      // initializing this MAC", which I have interpreted to mean the following precondition:
      requires params.KeyParameter?
      modifies this
      ensures
        var key := match params case KeyParameter(key) => key;
        match initialized { case Some(k) => validKey(k) && key == k case None => false }
      ensures InputSoFar == []

    method {:extern "Update"} updateSingle(input: uint8)
      requires initialized.Some?
      modifies this
      ensures unchanged(`initialized)
      ensures InputSoFar == old(InputSoFar) + [input]

    method {:extern "BlockUpdate"} update(input: seq<uint8>, inOff: int32, len: int32)
      requires initialized.Some?
      requires inOff >= 0
      requires len >= 0
      requires |input| < INT32_MAX_LIMIT
      requires inOff as int + len as int <= |input|
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff..(inOff + len)]

    method {:extern "GetResult"} getResult() returns (s: seq<uint8>)
      requires initialized.Some?
      requires algorithm != IDENTITY
      modifies `InputSoFar
      ensures InputSoFar == []
      ensures |s| == HashLength(algorithm) as int

    method updateAll(input: seq<uint8>)
      requires initialized.Some?
      requires |input| < INT32_MAX_LIMIT
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input
    {
      update(input, 0, |input| as int32);
    }
  }
}
