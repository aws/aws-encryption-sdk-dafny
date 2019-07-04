include "../Digests.dfy"
include "../../Util/StandardLibrary.dfy"

module {:extern "BouncyCastleCryptoMac"} BouncyCastleCryptoMac {
  import opened Digests
  import opened StandardLibrary
 
  datatype {:extern "CipherParameters"} CipherParameters = KeyParameter(key: array<byte>) // unsupported: other parameters

  // https://people.eecs.berkeley.edu/~jonah/bc/org/bouncycastle/crypto/Mac.html
  trait {:extern "Mac"} Mac {
 
    // The algorithm of a Mac object never changes. This is modeled by a constant ghost field.
    // The name of the algorithm can be retrieved by the "getAlgorithm" method.
    const {:extern "algorithm"} algorithm: HMAC_ALGORITHM
    function method {:extern "getAlgorithmName"} getAlgorithmName(): string
      ensures this.algorithm == HmacSHA256 ==> getAlgorithmName() == "SHA256"
      ensures this.algorithm == HmacSHA384 ==> getAlgorithmName() == "SHA384"
 
    // I'm guessing that the algorithm determines the length of the hash-function output once
    // and for all.
    function method {:extern "getMacSize"} getMacSize(): nat
      reads this  // allow the implementation to read fields of the object
      ensures getMacSize() == HashLength(algorithm)
 
 
    // To be useful, a Mac object must be associated with a key. This association is performed
    // by the "init" method.  The "init" method can be called at any time to reset the state of
    // the object and associate it with a new key.
    // Ghost field "initialized" keeps track of whether or not the Mac object has been initialized
    // and, if so, which key material is associated with it.
    ghost var initialized: Option<seq<byte>>

    predicate {:axiom} validKey(key: seq<byte>)

    method {:extern "init"} init(params: CipherParameters)
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
    ghost var InputSoFar: seq<byte>
 
    method {:extern "reset"} reset()
      // BouncyCastle's documentation doesn't mention the following precondition, and it doesn't
      // admit to any exception ever being thrown by the "reset" method. However, the documentation
      // of "reset" talks about the "previously initialized" state of the object, which suggests
      // that the object must already be initialized.
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []
  
    method {:extern "updateSingle"} updateSingle(input: byte)
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + [input]
 
    method {:extern "update"} update(input: array<byte>, inOff: nat, len: nat)
      requires initialized.Some?
      requires inOff + len <= input.Length
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff..inOff+len]

    // returns an int, but it is not specified, what that int stands for
    method {:extern "doFinal"} doFinal(output: array<byte>, outOff: nat) returns (retVal: int)
      requires initialized.Some?
      requires outOff + getMacSize() <= output.Length
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize()
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

    constructor {:extern} (algorithm: HMAC_ALGORITHM) 
      ensures this.algorithm == algorithm

    function method {:extern "getAlgorithmName"} getAlgorithmName(): string
      ensures this.algorithm == HmacSHA256 ==> getAlgorithmName() == "SHA256"
      ensures this.algorithm == HmacSHA384 ==> getAlgorithmName() == "SHA384"
 
    // I'm guessing that the algorithm determines the length of the hash-function output once
    // and for all.
    function method {:extern "getMacSize"} getMacSize(): nat
      reads this  // allow the implementation to read fields of the object
      ensures getMacSize() == HashLength(algorithm)

    predicate {:axiom} validKey(key: seq<byte>)

    method {:extern "init"} init(params: CipherParameters)
      // The documentation says it can throw "InvalidKeyException - if the given key is inappropriate for
      // initializing this MAC", which I have interpreted to mean the following precondition:
      //requires key.algorithm == algorithm
      requires params.KeyParameter?
      modifies this
      ensures
        var key := match params case KeyParameter(key) => key;
        match initialized { case Some(k) => validKey(k) && key[..] == k case None => false }
      ensures InputSoFar == [] 
 
    method {:extern "reset"} reset()
      // BouncyCastle's documentation doesn't mention the following precondition, and it doesn't
      // admit to any exception ever being thrown by the "reset" method. However, the documentation
      // of "reset" talks about the "previously initialized" state of the object, which suggests
      // that the object must already be initialized.
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []
 
    method {:extern "updateSingle"} updateSingle(input: byte)
      requires initialized.Some?
      modifies this
      ensures unchanged(`initialized)
      ensures InputSoFar == old(InputSoFar) + [input]
 
    method {:extern "update"} update(input: array<byte>, inOff: nat, len: nat)
      requires initialized.Some?
      requires inOff + len <= input.Length
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff..inOff+len]
      
    // returns an int, but it is not specified, what that int stands for
    method {:extern "doFinal"} doFinal(output: array<byte>, outOff: nat) returns (retVal: int)
      requires initialized.Some?
      requires outOff + getMacSize() <= output.Length
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize()
      modifies `InputSoFar, output
      ensures output[..] == old(output[..outOff]) + old(Hash(algorithm, initialized.get, InputSoFar)) + old(output[outOff + getMacSize()..])
      ensures output.Length == old(output.Length)
      ensures InputSoFar == []

    function method {:extern "getUnderlyingDigest"} getUnderlyingDigest(): HMAC_ALGORITHM
      ensures getUnderlyingDigest() == algorithm

    /*
     * End of BouncyCastle library functions
     */
    
    /*
     * Derived methods:
     * These might have "simpler" post-conditions that have better verification behaviour
     */
    method updateAll(input: array<byte>)
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[..]
    {
      update(input, 0, input.Length);
    }
  }
}