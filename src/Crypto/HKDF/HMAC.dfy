include "../Digests.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module {:extern "HMAC"} HMAC {
  import opened Digests
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  datatype {:extern "CipherParameters"} CipherParameters = KeyParameter(key: array<uint8>) // unsupported: other parameters

  // https://people.eecs.berkeley.edu/~jonah/bc/org/bouncycastle/crypto/Mac.html
  trait {:extern "Mac"} Mac {

    // The algorithm of a Mac object never changes. This is modeled by a constant ghost field.
    // The name of the algorithm can be retrieved by the "getAlgorithm" method.
    const {:extern "algorithm"} algorithm: KEY_DERIVATION_ALGORITHM
    function method {:extern "GetAlgorithmName"} getAlgorithmName(): string
      ensures this.algorithm == HKDF_WITH_SHA_256 ==> getAlgorithmName() == "SHA256"
      ensures this.algorithm == HKDF_WITH_SHA_384 ==> getAlgorithmName() == "SHA384"

    // I'm guessing that the algorithm determines the length of the hash-function output once
    // and for all.
    function method {:extern "GetMacSize"} getMacSize(): int32
      reads this  // allow the implementation to read fields of the object
      ensures getMacSize() == HashLength(algorithm)


    // To be useful, a Mac object must be associated with a key. This association is performed
    // by the "init" method.  The "init" method can be called at any time to reset the state of
    // the object and associate it with a new key.
    // Ghost field "initialized" keeps track of whether or not the Mac object has been initialized
    // and, if so, which key material is associated with it.
    ghost var initialized: Option<seq<uint8>>

    predicate {:axiom} validKey(key: seq<uint8>)

    method {:extern "Init"} init(params: CipherParameters)
      // The documentation says it can throw "InvalidKeyException - if the given key is inappropriate for
      // initializing this MAC", which I have interpreted to mean the following precondition:
      requires params.KeyParameter?
      modifies this
      ensures
        var key := match params case KeyParameter(key) => key;
        match initialized { case Some(k) => validKey(k) && key[..] == k case None => false }
      ensures InputSoFar == []

    // Once a key has been associated with the Mac object, calls to "update*" start
    // accumulating input that can be used to produce a MAC.  The accumulated input is modeled by
    // the ghost field "InputSoFar".
    // The act of resetting the object (which is done by the method "reset") is
    // to clear out any previous MAC computation. In other words, resetting the object sets "InputSoFar"
    // to the empty sequence (but leaves unchanged the key and algorithm of the Mac object).
    // The method  "doFinal" outputs the hash of the accumulated input and resets the accumulated
    // input "InputSoFar" to the empty sequence (but leaves unchanged the key and algorithm of the Mac
    // object).
    ghost var InputSoFar: seq<uint8>

    method {:extern "Reset"} reset()
      // BouncyCastle's documentation doesn't mention the following precondition, and it doesn't
      // admit to any exception ever being thrown by the "reset" method. However, the documentation
      // of "reset" talks about the "previously initialized" state of the object, which suggests
      // that the object must already be initialized.
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []

    method {:extern "Update"} updateSingle(input: uint8)
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + [input]

    method {:extern "BlockUpdate"} update(input: array<uint8>, inOff: int32, len: int32)
      requires initialized.Some?
      requires inOff >= 0
      requires len >= 0
      requires inOff as int + len as int <= input.Length
      requires input.Length < 0x8000_0000
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff..inOff+len]

    // returns an int, but it is not specified, what that int stands for
    method {:extern "DoFinal"} doFinal(output: array<uint8>, outOff: int32) returns (retVal: int32)
      requires initialized.Some?
      requires outOff >= 0
      requires outOff as int + getMacSize() as int <= output.Length
      requires output.Length < 0x8000_0000
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize() as int
      modifies `InputSoFar, output
      ensures output[..] == old(output[..outOff]) + old(Hash(algorithm, initialized.get, InputSoFar)) + old(output[outOff + getMacSize()..])
      ensures output.Length == old(output.Length)
      ensures InputSoFar == []
  }

  // https://people.eecs.berkeley.edu/~jonah/bc/org/bouncycastle/crypto/HMac.html
  class {:extern "HMac"} HMac extends Mac {

    /*
     * Beginning of BouncyCastle library functions
     */

    constructor {:extern} (algorithm: KEY_DERIVATION_ALGORITHM)
      ensures this.algorithm == algorithm

    function method {:extern "GetAlgorithmName"} getAlgorithmName(): string
      ensures this.algorithm == HKDF_WITH_SHA_256 ==> getAlgorithmName() == "SHA256"
      ensures this.algorithm == HKDF_WITH_SHA_384 ==> getAlgorithmName() == "SHA384"

    // I'm guessing that the algorithm determines the length of the hash-function output once
    // and for all.
    function method {:extern "GetMacSize"} getMacSize(): int32
      reads this  // allow the implementation to read fields of the object
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
      // BouncyCastle's documentation doesn't mention the following precondition, and it doesn't
      // admit to any exception ever being thrown by the "reset" method. However, the documentation
      // of "reset" talks about the "previously initialized" state of the object, which suggests
      // that the object must already be initialized.
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

    // returns an int, but it is not specified, what that int stands for
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

    function method {:extern "GetUnderlyingDigest"} getUnderlyingDigest(): KEY_DERIVATION_ALGORITHM
      ensures getUnderlyingDigest() == algorithm

    /*
     * End of BouncyCastle library functions
     */

    /*
     * Derived methods:
     * These might have "simpler" post-conditions that have better verification behaviour
     */
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
