// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net5.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 3.2.0.30713
// Command Line Options: /out:obj/Debug/netstandard2.0/GeneratedFromDafny.cs ../../src/Crypto/AESEncryption.dfy ../../src/Crypto/Datatypes.dfy ../../src/Crypto/Digest.dfy ../../src/Crypto/EncryptionSuites.dfy ../../src/Crypto/HKDF/HKDF.dfy ../../src/Crypto/HKDF/HMAC.dfy ../../src/Crypto/KeyDerivationAlgorithms.dfy ../../src/Crypto/Random.dfy ../../src/Crypto/RSAEncryption.dfy ../../src/Crypto/Signature.dfy ../../src/Generated/Aws.dfy ../../src/Generated/AwsCryptographicMaterialProviders.dfy ../../src/Generated/AwsEncryptionSdk.dfy ../../src/KMS/AmazonKeyManagementService.dfy ../../src/KMS/AwsKmsArnParsing.dfy ../../src/KMS/KMSUtils.dfy ../../src/SDK/AlgorithmSuite.dfy ../../src/SDK/AwsCryptographicMaterialProviders.dfy ../../src/SDK/AwsEncryptionSdk.dfy ../../src/SDK/CMM/DefaultCMM.dfy ../../src/SDK/Deserialize.dfy ../../src/SDK/EncryptDecrypt.dfy ../../src/SDK/EncryptionContext.dfy ../../src/SDK/Keyring/AwsKms/AwsKmsMrkAreUnique.dfy ../../src/SDK/Keyring/AwsKms/AwsKmsMrkAwareSymmetricKeyring.dfy ../../src/SDK/Keyring/AwsKms/AwsKmsMrkMatchForDecrypt.dfy ../../src/SDK/Keyring/AwsKms/Constants.dfy ../../src/SDK/Keyring/Defs.dfy ../../src/SDK/Keyring/RawAESKeyring.dfy ../../src/SDK/Materials.dfy ../../src/SDK/MessageBody.dfy ../../src/SDK/MessageHeader.dfy ../../src/SDK/Serialize.dfy ../../src/StandardLibrary/Actions.dfy ../../src/StandardLibrary/Base64.dfy ../../src/StandardLibrary/Base64Lemmas.dfy ../../src/StandardLibrary/StandardLibrary.dfy ../../src/StandardLibrary/UInt.dfy ../../src/Util/Sets.dfy ../../src/Util/Sorting.dfy ../../src/Util/Streams.dfy ../../src/Util/Time.dfy ../../src/Util/UTF8.dfy /compile:0 /spillTargetCode:3 /noVerify
// the_program


module {:extern ""AESEncryption""} AESEncryption {

  import EncryptionSuites = EncryptionSuites

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  export
    provides AESDecrypt, AESEncrypt, AESDecryptExtern, AESEncryptExtern, EncryptionSuites, Wrappers, UInt, PlaintextDecryptedWithAAD, EncryptionOutputEncryptedWithAAD, CiphertextGeneratedWithPlaintext, EncryptedWithKey, DecryptedWithKey
    reveals EncryptionOutput

  datatype EncryptionOutput = EncryptionOutput(cipherText: seq<uint8>, authTag: seq<uint8>)

  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
    decreases plaintext, aad

  predicate {:axiom} EncryptionOutputEncryptedWithAAD(ciphertext: EncryptionOutput, aad: seq<uint8>)
    decreases ciphertext, aad

  predicate {:axiom} CiphertextGeneratedWithPlaintext(ciphertext: seq<uint8>, plaintext: seq<uint8>)
    decreases ciphertext, plaintext

  predicate {:axiom} EncryptedWithKey(ciphertext: seq<uint8>, key: seq<uint8>)
    decreases ciphertext, key

  predicate {:axiom} DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)
    decreases key, plaintext

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: EncryptionSuites.EncryptionSuite): (encArt: EncryptionOutput)
    requires encAlg.Valid()
    requires |s| >= encAlg.tagLen as int
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLen as int
    decreases s, encAlg
  {
    EncryptionOutput(s[..|s| - encAlg.tagLen as int], s[|s| - encAlg.tagLen as int..])
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESEncryptExtern""} AESEncryptExtern(encAlg: EncryptionSuites.EncryptionSuite, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<EncryptionOutput, string>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |iv| == encAlg.ivLen as int
    requires |key| == encAlg.keyLen as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)
    decreases encAlg, iv, key, msg, aad

  method AESEncrypt(encAlg: EncryptionSuites.EncryptionSuite, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<EncryptionOutput, string>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |iv| == encAlg.ivLen as int
    requires |key| == encAlg.keyLen as int
    ensures res.Success? ==> |res.value.cipherText| == |msg| && |res.value.authTag| == encAlg.tagLen as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)
    decreases encAlg, iv, key, msg, aad
  {
    res := AESEncryptExtern(encAlg, iv, key, msg, aad);
    if res.Success? && |res.value.cipherText| != |msg| {
      res := Failure(""AESEncrypt did not return cipherText of expected length"");
    }
    if res.Success? && |res.value.authTag| != encAlg.tagLen as int {
      res := Failure(""AESEncryption did not return valid tag"");
    }
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESDecryptExtern""} AESDecryptExtern(encAlg: EncryptionSuites.EncryptionSuite, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |key| == encAlg.keyLen as int
    requires |iv| == encAlg.ivLen as int
    requires |authTag| == encAlg.tagLen as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    decreases encAlg, key, cipherTxt, authTag, iv, aad

  method AESDecrypt(encAlg: EncryptionSuites.EncryptionSuite, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |key| == encAlg.keyLen as int
    requires |iv| == encAlg.ivLen as int
    requires |authTag| == encAlg.tagLen as int
    ensures res.Success? ==> |res.value| == |cipherTxt|
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    decreases encAlg, key, cipherTxt, authTag, iv, aad
  {
    res := AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);
    if res.Success? && |cipherTxt| != |res.value| {
      res := Failure(""AESDecrypt did not return plaintext of expected length"");
    }
  }
}

module CryptoDatatypes {
  datatype DigestAlgorithm = SHA_512
}

module Digest {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import CryptoDatatypes = CryptoDatatypes

  import ExternDigest = ExternDigest
  function method Length(alg: CryptoDatatypes.DigestAlgorithm): nat
    decreases alg
  {
    match alg
    case SHA_512() =>
      64
  }

  method Digest(alg: CryptoDatatypes.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, string>)
    ensures res.Success? ==> |res.value| == Length(alg)
    decreases alg, msg
  {
    var result := ExternDigest.Digest(alg, msg);
    if result.Success? && |result.value| != Length(alg) {
      return Failure(""Incorrect length digest from ExternDigest."");
    }
    return result;
  }
}

module {:extern ""ExternDigest""} ExternDigest {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened CryptoDatatypes = CryptoDatatypes
  method {:extern} Digest(alg: CryptoDatatypes.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, string>)
    decreases alg, msg
}

module {:extern ""EncryptionSuites""} EncryptionSuites {

  import opened UInt = StandardLibrary.UInt
  datatype EncryptionAlgorithm = AES(mode: AESMode)

  datatype AESMode = GCM

  datatype EncryptionSuite = EncryptionSuite(alg: EncryptionAlgorithm, keyLen: uint8, tagLen: uint8, ivLen: uint8) {
    predicate method Valid()
      decreases this
    {
      match alg
      case AES(mode) =>
        keyLen as int in AES_CIPHER_KEY_LENGTHS &&
        tagLen == AES_TAG_LEN &&
        ivLen == AES_IV_LEN &&
        mode == GCM
    }
  }

  const AES_MAX_KEY_LEN := 32
  const AES_CIPHER_KEY_LENGTHS := {32, 24, 16}
  const AES_TAG_LEN := 16 as uint8
  const AES_IV_LEN := 12 as uint8
  const AES_GCM_128 := EncryptionSuite(AES(GCM), 16, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_192 := EncryptionSuite(AES(GCM), 24, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_256 := EncryptionSuite(AES(GCM), 32, AES_TAG_LEN, AES_IV_LEN)
}

module HKDF {

  import opened HMAC = HMAC

  import opened KeyDerivationAlgorithms = KeyDerivationAlgorithms

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  function method GetHMACDigestFromHKDFAlgorithm(algorithm: HKDFAlgorithms): Digests
    decreases algorithm
  {
    match algorithm
    case HKDF_WITH_SHA_256() =>
      SHA_256
    case HKDF_WITH_SHA_384() =>
      SHA_384
  }

  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>, ghost digest: Digests)
      returns (prk: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures GetHashLength(hmac.GetDigest()) == |prk|
    ensures hmac.GetKey() == salt
    ensures hmac.GetDigest() == digest
    decreases hmac, salt, ikm, digest
  {
    hmac.Init(salt);
    hmac.Update(ikm);
    assert hmac.GetInputSoFar() == ikm;
    prk := hmac.GetResult();
    return prk;
  }

  predicate T(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then
      [] == res
    else
      ghost var nMinusOne: int := n - 1; exists prev1: seq<uint8>, prev2: seq<uint8> :: T(hmac, info, nMinusOne, prev1) && Ti(hmac, info, n, prev2) && prev1 + prev2 == res
  }

  predicate Ti(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n, 1
  {
    if n == 0 then
      res == []
    else
      exists prev: seq<uint8> :: PreTi(hmac, info, n, prev) && hmac.HashSignature(prev, res)
  }

  predicate PreTi(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 1 <= n < 256
    decreases n, 0
  {
    ghost var nMinusOne: int := n - 1;
    exists prev: seq<uint8> | Ti(hmac, info, nMinusOne, prev) :: 
      res == prev + info + [n as uint8]
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, expectedLength: int, digest: Digests, ghost salt: seq<uint8>)
      returns (okm: seq<uint8>, ghost okmUnabridged: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires 1 <= expectedLength <= 255 * GetHashLength(hmac.GetDigest())
    requires |salt| != 0
    requires hmac.GetKey() == salt
    requires |info| < INT32_MAX_LIMIT
    requires GetHashLength(hmac.GetDigest()) == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.GetKey() == prk
    ensures var n: int := (GetHashLength(digest) + expectedLength - 1) / GetHashLength(digest); T(hmac, info, n, okmUnabridged) && (|okmUnabridged| <= expectedLength ==> okm == okmUnabridged) && (expectedLength < |okmUnabridged| ==> okm == okmUnabridged[..expectedLength])
    decreases hmac, prk, info, expectedLength, digest, salt
  {
    var hashLength := GetHashLength(digest);
    var n := (hashLength + expectedLength - 1) / hashLength;
    assert 0 <= n < 256;
    hmac.Init(prk);
    var t_prev := [];
    var t_n := t_prev;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |t_prev| == if i == 1 then 0 else hashLength
      invariant hashLength == |prk|
      invariant |t_n| == (i - 1) * hashLength
      invariant hmac.GetKey() == prk
      invariant hmac.GetDigest() == digest
      invariant hmac.GetInputSoFar() == []
      invariant T(hmac, info, i - 1, t_n)
      invariant Ti(hmac, info, i - 1, t_prev)
      decreases n - i
    {
      hmac.Update(t_prev);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.GetInputSoFar() == t_prev + info + [i as uint8];
      t_prev := hmac.GetResult();
      assert Ti(hmac, info, i, t_prev);
      t_n := t_n + t_prev;
      i := i + 1;
      assert T(hmac, info, i - 1, t_n);
    }
    okm := t_n;
    okmUnabridged := okm;
    assert T(hmac, info, n, okmUnabridged);
    if expectedLength < |okm| {
      okm := okm[..expectedLength];
    }
  }

  method Hkdf(algorithm: HKDFAlgorithms, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int)
      returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * GetHashLength(GetHMACDigestFromHKDFAlgorithm(algorithm))
    requires salt.None? || |salt.value| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
    decreases algorithm, salt, ikm, info, L
  {
    if L == 0 {
      return [];
    }
    var digest := GetHMACDigestFromHKDFAlgorithm(algorithm);
    var hmac := new HMac(digest);
    var hashLength := GetHashLength(digest);
    var nonEmptySalt: seq<uint8>;
    match salt {
      case {:split false} None() =>
        nonEmptySalt := StandardLibrary.Fill(0, hashLength);
      case {:split false} Some(s) =>
        nonEmptySalt := s;
    }
    var prk := Extract(hmac, nonEmptySalt, ikm, digest);
    ghost var okmUnabridged;
    okm, okmUnabridged := Expand(hmac, prk, info, L, digest, nonEmptySalt);
  }
}

module {:extern ""HMAC""} HMAC {

  import opened KeyDerivationAlgorithms = KeyDerivationAlgorithms

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""Digests""} Digests = SHA_256 | SHA_384

  class {:extern ""HMac""} HMac {
    function {:extern} GetKey(): seq<uint8>
      reads this
      decreases {this}

    function {:extern} GetDigest(): Digests
      reads this
      decreases {this}

    function {:extern} GetInputSoFar(): seq<uint8>
      reads this
      decreases {this}

    constructor {:extern} (digest: Digests)
      ensures this.GetDigest() == digest
      ensures this.GetInputSoFar() == []
      decreases digest

    method {:extern ""Init""} Init(key: seq<uint8>)
      modifies this
      ensures this.GetKey() == key
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetInputSoFar() == []
      decreases key

    method {:extern ""BlockUpdate""} Update(input: seq<uint8>)
      requires |this.GetKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.GetInputSoFar() == old(this.GetInputSoFar()) + input
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      decreases input

    method {:extern ""GetResult""} GetResult() returns (s: seq<uint8>)
      requires |this.GetKey()| > 0
      modifies this
      ensures |s| == GetHashLength(this.GetDigest())
      ensures this.GetInputSoFar() == []
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      ensures this.HashSignature(old(this.GetInputSoFar()), s)

    predicate {:axiom} HashSignature(message: seq<uint8>, s: seq<uint8>)
      decreases message, s
  }

  function method GetHashLength(digest: Digests): int
    decreases digest
  {
    match digest
    case SHA_256() =>
      32
    case SHA_384() =>
      48
  }
}

module {:extern ""KeyDerivationAlgorithms""} KeyDerivationAlgorithms {

  import opened UInt = StandardLibrary.UInt
  datatype KeyDerivationAlgorithm = HKDF_WITH_SHA_384 | HKDF_WITH_SHA_256 | IDENTITY

  type HKDFAlgorithms = a: KeyDerivationAlgorithm
    | a != KeyDerivationAlgorithm.IDENTITY
    witness KeyDerivationAlgorithm.HKDF_WITH_SHA_384

  type IdentityAlgorithm = a: KeyDerivationAlgorithm
    | a == KeyDerivationAlgorithm.IDENTITY
    witness KeyDerivationAlgorithm.IDENTITY
}

module Random {

  export
    provides GenerateBytes, Wrappers, UInt


  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import ExternRandom = ExternRandom
  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, string>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
    decreases i
  {
    var result := ExternRandom.GenerateBytes(i);
    if result.Success? && |result.value| != i as int {
      return Failure(""Incorrect length from ExternRandom."");
    }
    return result;
  }
}

module {:extern ""ExternRandom""} ExternRandom {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, string>)
    decreases i
}

module {:extern ""RSAEncryption""} RSAEncryption {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""PaddingMode""} PaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

  newtype {:nativeType ""int"", ""number""} StrengthBits = x: int
    | 81 <= x < 2147483648
    witness 81

  trait {:termination false} Key {
    ghost var Repr: set<object>
    ghost const strength: StrengthBits
    ghost const padding: PaddingMode
    const pem: seq<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      |pem| > 0 &&
      GetBytes(strength) >= MinStrengthBytes(padding) &&
      PEMGeneratedWithStrength(pem, strength) &&
      PEMGeneratedWithPadding(pem, padding)
    }
  }

  class PrivateKey extends Key {
    constructor (pem: seq<uint8>, ghost strength: StrengthBits, ghost padding: PaddingMode)
      requires |pem| > 0
      requires GetBytes(strength) >= MinStrengthBytes(padding)
      requires PEMGeneratedWithStrength(pem, strength)
      requires PEMGeneratedWithPadding(pem, padding)
      ensures this.pem == pem
      ensures this.strength == strength
      ensures this.padding == padding
      ensures Valid() && fresh(Repr)
      decreases pem, strength, padding
    {
      this.pem := pem;
      this.strength := strength;
      this.padding := padding;
      Repr := {this};
    }
  }

  class PublicKey extends Key {
    constructor (pem: seq<uint8>, ghost strength: StrengthBits, ghost padding: PaddingMode)
      requires |pem| > 0
      requires GetBytes(strength) >= MinStrengthBytes(padding)
      requires PEMGeneratedWithStrength(pem, strength)
      requires PEMGeneratedWithPadding(pem, padding)
      ensures this.pem == pem
      ensures this.strength == strength
      ensures this.padding == padding
      ensures Valid() && fresh(Repr)
      decreases pem, strength, padding
    {
      this.pem := pem;
      this.strength := strength;
      this.padding := padding;
      Repr := {this};
    }
  }

  predicate {:axiom} PEMGeneratedWithStrength(pem: seq<uint8>, strength: StrengthBits)
    decreases pem, strength

  predicate {:axiom} PEMGeneratedWithPadding(pem: seq<uint8>, padding: PaddingMode)
    decreases pem, padding

  const SHA1_HASH_BYTES := 20
  const SHA256_HASH_BYTES := 32
  const SHA384_HASH_BYTES := 48
  const SHA512_HASH_BYTES := 64

  function GetBytes(bits: StrengthBits): nat
    decreases bits
  {
    (bits as nat + 7) / 8
  }

  function MinStrengthBytes(padding: PaddingMode): nat
    decreases padding
  {
    match padding {
      case PKCS1() =>
        11
      case OAEP_SHA1() =>
        2 * SHA1_HASH_BYTES + 2
      case OAEP_SHA256() =>
        2 * SHA256_HASH_BYTES + 2
      case OAEP_SHA384() =>
        2 * SHA384_HASH_BYTES + 2
      case OAEP_SHA512() =>
        2 * SHA512_HASH_BYTES + 2
    }
  }

  function MaxPlaintextBytes(padding: PaddingMode, strength: StrengthBits): nat
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    decreases padding, strength
  {
    match padding {
      case PKCS1() =>
        GetBytes(strength) - 11
      case OAEP_SHA1() =>
        GetBytes(strength) - 2 * SHA1_HASH_BYTES - 2
      case OAEP_SHA256() =>
        GetBytes(strength) - 2 * SHA256_HASH_BYTES - 2
      case OAEP_SHA384() =>
        GetBytes(strength) - 2 * SHA384_HASH_BYTES - 2
      case OAEP_SHA512() =>
        GetBytes(strength) - 2 * SHA512_HASH_BYTES - 2
    }
  }

  method GenerateKeyPair(strength: StrengthBits, padding: PaddingMode)
      returns (publicKey: PublicKey, privateKey: PrivateKey)
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    ensures privateKey.Valid() && fresh(privateKey.Repr)
    ensures privateKey.strength == strength
    ensures privateKey.padding == padding
    ensures publicKey.Valid() && fresh(publicKey.Repr)
    ensures publicKey.strength == strength
    ensures publicKey.padding == padding
    ensures GetBytes(publicKey.strength) >= MinStrengthBytes(publicKey.padding)
    ensures GetBytes(privateKey.strength) >= MinStrengthBytes(privateKey.padding)
    decreases strength, padding
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(strength, padding);
    privateKey := new PrivateKey(pemPrivate, strength, padding);
    publicKey := new PublicKey(pemPublic, strength, padding);
  }

  method Decrypt(padding: PaddingMode, privateKey: PrivateKey, cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires privateKey.Valid()
    requires 0 < |cipherText|
    requires padding == privateKey.padding
    ensures privateKey.Valid()
    decreases padding, privateKey, cipherText
  {
    res := DecryptExtern(padding, privateKey.pem, cipherText);
  }

  method Encrypt(padding: PaddingMode, publicKey: PublicKey, plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires publicKey.Valid()
    requires GetBytes(publicKey.strength) >= MinStrengthBytes(padding)
    requires 0 < |plaintextData|
    requires padding == publicKey.padding
    ensures publicKey.Valid()
    decreases padding, publicKey, plaintextData
  {
    res := EncryptExtern(padding, publicKey.pem, plaintextData);
  }

  method {:extern ""RSAEncryption.RSA"", ""GenerateKeyPairExtern""} GenerateKeyPairExtern(strength: StrengthBits, padding: PaddingMode)
      returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    requires GetBytes(strength) >= MinStrengthBytes(padding)
    ensures |publicKey| > 0
    ensures |privateKey| > 0
    ensures PEMGeneratedWithStrength(publicKey, strength)
    ensures PEMGeneratedWithStrength(privateKey, strength)
    ensures PEMGeneratedWithPadding(publicKey, padding)
    ensures PEMGeneratedWithPadding(privateKey, padding)
    decreases strength, padding

  method {:extern ""RSAEncryption.RSA"", ""DecryptExtern""} DecryptExtern(padding: PaddingMode, privateKey: seq<uint8>, cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |privateKey| > 0
    requires |cipherText| > 0
    decreases padding, privateKey, cipherText

  method {:extern ""RSAEncryption.RSA"", ""EncryptExtern""} EncryptExtern(padding: PaddingMode, publicKey: seq<uint8>, plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
    decreases padding, publicKey, plaintextData
}

module {:extern ""Signature""} Signature {

  export
    reveals SignatureKeyPair, ECDSAParams, ECDSAParams.SignatureLength, ECDSAParams.FieldSize
    provides KeyGen, Sign, Verify, IsSigned, Wrappers, UInt


  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  datatype ECDSAParams = ECDSA_P384 | ECDSA_P256 {
    function method SignatureLength(): uint16
      decreases this
    {
      match this
      case ECDSA_P256() =>
        71
      case ECDSA_P384() =>
        103
    }

    function method FieldSize(): nat
      decreases this
    {
      match this
      case ECDSA_P256() =>
        assert 1 + (256 + 7) / 8 == 33; 33
      case ECDSA_P384() =>
        assert 1 + (384 + 7) / 8 == 49;
        49
    }
  }

  predicate {:axiom} IsSigned(key: seq<uint8>, msg: seq<uint8>, signature: seq<uint8>)
    decreases key, msg, signature

  method KeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair, string>)
    ensures match res { case Success(_mcc#0) => (var sigKeyPair := _mcc#0; |sigKeyPair.verificationKey| == s.FieldSize()) case Failure(_mcc#1) => true }
    decreases s
  {
    var sigKeyPair :- ExternKeyGen(s);
    if |sigKeyPair.verificationKey| == s.FieldSize() {
      return Success(sigKeyPair);
    } else {
      return Failure(""Incorrect verification-key length from ExternKeyGen."");
    }
  }

  method {:extern ""Signature.ECDSA"", ""ExternKeyGen""} ExternKeyGen(s: ECDSAParams) returns (res: Result<SignatureKeyPair, string>)
    decreases s

  method {:extern ""Signature.ECDSA"", ""Sign""} Sign(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>)
      returns (sig: Result<seq<uint8>, string>)
    ensures sig.Success? ==> IsSigned(key, msg, sig.value)
    decreases s, key, msg

  method {:extern ""Signature.ECDSA"", ""Verify""} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>)
      returns (res: Result<bool, string>)
    decreases s, key, msg, sig
}

module {:extern ""Dafny.Aws""} Aws {

  module {:extern ""Dafny.Aws.Crypto""} Crypto {

    import opened Wrappers = Wrappers

    import AmazonKeyManagementService = AmazonKeyManagementService

    import opened UInt = StandardLibrary.UInt

    import UTF8 = UTF8

    export
      provides UTF8, UInt, Wrappers, IKeyring.OnDecrypt, ICryptographicMaterialsManager.GetEncryptionMaterials, ICryptographicMaterialsManager.DecryptMaterials, IKeyring.OnEncrypt, IAwsCryptographicMaterialsProviderClient.CreateRawAesKeyring, IAwsCryptographicMaterialsProviderClient.CreateDefaultCryptographicMaterialsManager
      reveals AlgorithmSuiteId, EncryptedDataKey, EncryptedDataKey.Valid, IKeyring, GetEncryptionMaterialsInput, GetEncryptionMaterialsOutput, DecryptMaterialsInput, DecryptMaterialsOutput, ICryptographicMaterialsManager, EncryptionContext, EncryptionMaterials, DecryptionMaterials, ValidEncryptedDataKey, EncryptedDataKeyList, OnEncryptInput, OnEncryptOutput, OnDecryptInput, OnDecryptOutput, OnEncryptInput.Valid, OnDecryptInput.Valid, GetEncryptionMaterialsInput.Valid, DecryptMaterialsInput.Valid, EncryptionMaterials.Valid, CreateRawAesKeyringInput, CreateDefaultCryptographicMaterialsManagerInput, IAwsCryptographicMaterialsProviderClient, AesWrappingAlg, CreateDefaultCryptographicMaterialsManagerInput.Valid, CreateRawAesKeyringInput.Valid

    type KmsKeyId = string

    type KmsKeyIdList = seq<KmsKeyId>

    type GrantToken = string

    type GrantTokenList = seq<GrantToken>

    type Region = string

    type RegionList = seq<Region>

    datatype DiscoveryFilter = DiscoveryFilter(accountId: string, partition: string) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetClientInput = GetClientInput(region: string) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait IKmsClient { }

    trait IClientSupplier {
      method GetClient(input: GetClientInput) returns (res: IKmsClient)
        requires input.Valid()
        decreases input
    }

    type EncryptionContext = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

    datatype EncryptedDataKey = EncryptedDataKey(nameonly keyProviderId: UTF8.ValidUTF8Bytes, nameonly keyProviderInfo: seq<uint8>, nameonly ciphertext: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        |keyProviderId| < UINT16_LIMIT &&
        |keyProviderInfo| < UINT16_LIMIT &&
        |ciphertext| < UINT16_LIMIT
      }
    }

    type ValidEncryptedDataKey = i: EncryptedDataKey
      | i.Valid()
      witness *

    type EncryptedDataKeyList = seq<EncryptedDataKey>

    datatype EncryptionMaterials = EncryptionMaterials(nameonly algorithmSuiteId: AlgorithmSuiteId, nameonly encryptionContext: EncryptionContext, nameonly encryptedDataKeys: seq<ValidEncryptedDataKey>, nameonly plaintextDataKey: Option<seq<uint8>>, nameonly signingKey: Option<seq<uint8>>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptionMaterials = DecryptionMaterials(nameonly algorithmSuiteId: AlgorithmSuiteId, nameonly encryptionContext: EncryptionContext, nameonly plaintextDataKey: Option<seq<uint8>>, nameonly verificationKey: Option<seq<uint8>>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CommitmentPolicy = FORBID_ENCRYPT_FORBID_DECRYPT | REQUIRE_ENCRYPT_ALLOW_DECRYPT | REQUIRE_ENCRYPT_REQUIRE_DECRYPT

    datatype AesWrappingAlg = ALG_AES128_GCM_IV12_TAG16 | ALG_AES192_GCM_IV12_TAG16 | ALG_AES256_GCM_IV12_TAG16

    datatype AlgorithmSuiteId = ALG_AES_128_GCM_IV12_TAG16_NO_KDF | ALG_AES_192_GCM_IV12_TAG16_NO_KDF | ALG_AES_256_GCM_IV12_TAG16_NO_KDF | ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 | ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 | ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 | ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 | ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 | ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384

    datatype PaddingScheme = PKCS1 | OAEP_SHA1_MGF1 | OAEP_SHA256_MGF1 | OAEP_SHA384_MGF1 | OAEP_SHA512_MGF1

    datatype OnEncryptInput = OnEncryptInput(nameonly materials: EncryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype OnEncryptOutput = OnEncryptOutput(nameonly materials: EncryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype OnDecryptInput = OnDecryptInput(nameonly materials: DecryptionMaterials, nameonly encryptedDataKeys: EncryptedDataKeyList) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype OnDecryptOutput = OnDecryptOutput(nameonly materials: DecryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait {:termination false} IKeyring {
      method OnEncrypt(input: OnEncryptInput) returns (res: Result<OnEncryptOutput, string>)
        requires input.Valid()
        decreases input

      method OnDecrypt(input: OnDecryptInput) returns (res: Result<OnDecryptOutput, string>)
        requires input.Valid()
        decreases input
    }

    datatype CacheUsageMetadata = CacheUsageMetadata(messageUsage: int64, byteUsage: int64) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype EncryptEntry = EncryptEntry(identifier: seq<uint8>, encryptionMaterials: EncryptionMaterials, creationTime: int64, expiryTime: int64, usageMetadata: CacheUsageMetadata) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptEntry = DecryptEntry(identifier: seq<uint8>, decryptionMaterials: DecryptionMaterials, creationTime: int64, expiryTime: int64, usageMetadata: CacheUsageMetadata) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype PutEntryForEncryptInput = PutEntryForEncryptInput(identifier: seq<uint8>, encryptionMaterials: EncryptionMaterials, usageMetadata: CacheUsageMetadata) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype PutEntryForEncryptOutput = PutEntryForEncryptOutput {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetEntryForEncryptInput = GetEntryForEncryptInput(identifier: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetEntryForEncryptOutput = GetEntryForEncryptOutput(cacheEntry: EncryptEntry) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype PutEntryForDecryptInput = PutEntryForDecryptInput(identifier: seq<uint8>, decryptionMaterials: DecryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype PutEntryForDecryptOutput = PutEntryForDecryptOutput {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetEntryForDecryptInput = GetEntryForDecryptInput(identifier: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetEntryForDecryptOutput = GetEntryForDecryptOutput(cacheEntry: DecryptEntry) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DeleteEntryInput = DeleteEntryInput(identifier: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DeleteEntryOutput = DeleteEntryOutput {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait ICryptoMaterialsCache {
      method PutEntryForEncrypt(input: PutEntryForEncryptInput) returns (res: PutEntryForEncryptOutput)
        requires input.Valid()
        decreases input

      method GetEntryForEncrypt(input: GetEntryForEncryptInput) returns (res: GetEntryForEncryptOutput)
        requires input.Valid()
        decreases input

      method PutEntryForDecrypt(input: PutEntryForDecryptInput) returns (res: PutEntryForDecryptOutput)
        requires input.Valid()
        decreases input

      method GetEntryForDecrypt(input: GetEntryForDecryptInput) returns (res: GetEntryForDecryptOutput)
        requires input.Valid()
        decreases input

      method DeleteEntry(input: DeleteEntryInput) returns (res: DeleteEntryOutput)
        requires input.Valid()
        decreases input
    }

    datatype GetEncryptionMaterialsInput = GetEncryptionMaterialsInput(nameonly encryptionContext: EncryptionContext, nameonly algorithmSuiteId: Option<AlgorithmSuiteId>, nameonly maxPlaintextLength: Option<int64>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype GetEncryptionMaterialsOutput = GetEncryptionMaterialsOutput(nameonly encryptionMaterials: EncryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptMaterialsInput = DecryptMaterialsInput(nameonly algorithmSuiteId: AlgorithmSuiteId, nameonly encryptedDataKeys: EncryptedDataKeyList, nameonly encryptionContext: EncryptionContext) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptMaterialsOutput = DecryptMaterialsOutput(nameonly decryptionMaterials: DecryptionMaterials) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait {:termination false} ICryptographicMaterialsManager {
      method GetEncryptionMaterials(input: GetEncryptionMaterialsInput) returns (res: Result<GetEncryptionMaterialsOutput, string>)
        requires input.Valid()
        decreases input

      method DecryptMaterials(input: DecryptMaterialsInput) returns (res: Result<DecryptMaterialsOutput, string>)
        requires input.Valid()
        decreases input
    }

    datatype CreateAwsKmsKeyringInput = CreateAwsKmsKeyringInput(nameonly clientSupplier: IClientSupplier, nameonly generator: Option<KmsKeyId>, nameonly keyIds: Option<KmsKeyIdList>, grantTokens: Option<GrantTokenList>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateMrkAwareStrictAwsKmsKeyringInput = CreateMrkAwareStrictAwsKmsKeyringInput(nameonly kmsKeyId: KmsKeyId, nameonly grantTokens: Option<GrantTokenList>, nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateMrkAwareStrictMultiKeyringInput = CreateMrkAwareStrictMultiKeyringInput(nameonly generator: Option<KmsKeyId>, nameonly kmsKeyIds: Option<KmsKeyIdList>, nameonly grantTokens: Option<GrantTokenList>, nameonly clientSupplier: IClientSupplier?) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateMrkAwareDiscoveryAwsKmsKeyringInput = CreateMrkAwareDiscoveryAwsKmsKeyringInput(nameonly kmsClient: AmazonKeyManagementService.IAmazonKeyManagementService, nameonly discoveryFilter: Option<DiscoveryFilter>, nameonly grantTokens: Option<GrantTokenList>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateMrkAwareDiscoveryMultiKeyringInput = CreateMrkAwareDiscoveryMultiKeyringInput(nameonly regions: RegionList, nameonly discoveryFilter: Option<DiscoveryFilter>, nameonly grantTokens: Option<GrantTokenList>, nameonly clientSupplier: IClientSupplier?) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateMultiKeyringInput = CreateMultiKeyringInput(nameonly generator: IKeyring?, nameonly childKeyrings: Option<seq<IKeyring>>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateRawAesKeyringInput = CreateRawAesKeyringInput(nameonly keyNamespace: string, nameonly keyName: string, nameonly wrappingKey: seq<uint8>, nameonly wrappingAlg: AesWrappingAlg) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateRawRsaKeyringInput = CreateRawRsaKeyringInput(nameonly keyNamespace: string, nameonly keyName: string, nameonly paddingScheme: PaddingScheme, nameonly publicKey: Option<seq<uint8>>, nameonly privateKey: Option<seq<uint8>>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateDefaultCryptographicMaterialsManagerInput = CreateDefaultCryptographicMaterialsManagerInput(nameonly keyring: IKeyring) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateCachingCryptographicMaterialsManagerInput = CreateCachingCryptographicMaterialsManagerInput(nameonly cache: ICryptoMaterialsCache, nameonly cacheLimitTtl: int32, nameonly keyring: IKeyring?, nameonly materialsManager: ICryptographicMaterialsManager?, nameonly partitionId: Option<string>, nameonly limitBytes: Option<int64>, nameonly limitMessages: Option<int64>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype CreateLocalCryptoMaterialsCacheInput = CreateLocalCryptoMaterialsCacheInput(nameonly entryCapacity: int32, nameonly entryPruningTailSize: Option<int32>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait {:termination false} IAwsCryptographicMaterialsProviderClient {
      method CreateRawAesKeyring(input: CreateRawAesKeyringInput) returns (res: IKeyring)
        requires input.Valid()
        decreases input

      method CreateDefaultCryptographicMaterialsManager(input: CreateDefaultCryptographicMaterialsManagerInput) returns (res: ICryptographicMaterialsManager)
        requires input.Valid()
        decreases input
    }
  }

  module {:extern ""Dafny.Aws.Esdk""} Esdk {

    import Crypto = Crypto

    import opened UInt = StandardLibrary.UInt

    import opened Wrappers = Wrappers
    datatype EncryptInput = EncryptInput(nameonly plaintext: seq<uint8>, nameonly encryptionContext: Crypto.EncryptionContext, nameonly materialsManager: Crypto.ICryptographicMaterialsManager, nameonly algorithmSuiteId: Option<Crypto.AlgorithmSuiteId>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype EncryptOutput = EncryptOutput(nameonly ciphertext: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptInput = DecryptInput(nameonly ciphertext: seq<uint8>, nameonly materialsManager: Crypto.ICryptographicMaterialsManager) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    datatype DecryptOutput = DecryptOutput(nameonly plaintext: seq<uint8>) {
      predicate Valid()
        decreases this
      {
        true
      }
    }

    trait {:termination false} IAwsEncryptionSdkClient {
      method Encrypt(input: EncryptInput) returns (res: Result<EncryptOutput, string>)
        requires input.Valid()
        decreases input

      method Decrypt(input: DecryptInput) returns (res: Result<DecryptOutput, string>)
        requires input.Valid()
        decreases input
    }
  }
}

module {:extern ""Amazon.KeyManagementService""} AmazonKeyManagementService {
  class {:extern ""IAmazonKeyManagementService""} IAmazonKeyManagementService { }
}

module AwsKmsArnParsing {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened Seq = Seq

  import UTF8 = UTF8
  datatype AwsResource = AwsResource(resourceType: string, value: string) {
    predicate method Valid()
      decreases this
    {
      true &&
      0 < |value|
    }

    function method ToString(): string
      decreases this
    {
      resourceType + ""/"" + value
    }
  }

  datatype AwsArn = AwsArn(arnLiteral: string, partition: string, service: string, region: string, account: string, resource: AwsResource) {
    predicate method Valid()
      decreases this
    {
      arnLiteral == ""arn"" &&
      0 < |partition| &&
      0 < |service| &&
      0 < |region| &&
      0 < |account| &&
      resource.Valid()
    }

    function method ToString(): string
      requires this.Valid()
      decreases this
    {
      ToArnString(None)
    }

    function method ToArnString(customRegion: Option<string>): string
      requires this.Valid()
      decreases if customRegion.None? then 1 else 0
    {
      match customRegion {
        case None() =>
          ToArnString(Some(region))
        case Some(customRegion) =>
          Join([arnLiteral, partition, service, customRegion, account, resource.ToString()], "":"")
      }
    }
  }

  type AwsKmsArn = a: AwsArn
    | ValidAwsKmsArn(a)
    witness *

  type AwsKmsResource = r: AwsResource
    | ValidAwsKmsResource(r)
    witness *

  datatype AwsKmsIdentifier = AwsKmsArnIdentifier(a: AwsKmsArn) | AwsKmsRawResourceIdentifier(r: AwsKmsResource) {
    function method ToString(): string
      decreases this
    {
      match this {
        case AwsKmsArnIdentifier(a) =>
          a.ToString()
        case AwsKmsRawResourceIdentifier(r) =>
          r.ToString()
      }
    }
  }

  type AwsKmsIdentifierString = s: string
    | ParseAwsKmsIdentifier(s).Success? && UTF8.IsASCIIString(s) && 0 < |s| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
    witness *

  const MAX_AWS_KMS_IDENTIFIER_LENGTH := 2048

  predicate method ValidAwsKmsResource(resource: AwsResource)
    decreases resource
  {
    resource.Valid() &&
    (resource.resourceType == ""key"" || resource.resourceType == ""alias"")
  }

  predicate method ValidAwsKmsArn(arn: AwsArn)
    decreases arn
  {
    arn.Valid() &&
    arn.service == ""kms"" &&
    ValidAwsKmsResource(arn.resource)
  }

  function method ParseAwsKmsRawResources(identifier: string): (result: Result<AwsKmsResource, string>)
    decreases identifier
  {
    var info: seq<seq<char>> := Split(identifier, '/');
    Need(info[0] != ""key"", ""Malformed raw key id: "" + identifier); if |info| == 1 then ParseAwsKmsResources(""key/"" + identifier) else ParseAwsKmsResources(identifier)
  }

  function method ParseAwsKmsResources(identifier: string): (result: Result<AwsKmsResource, string>)
    decreases identifier
  {
    var info: seq<seq<char>> := Split(identifier, '/');
    Need(|info| > 1, ""Malformed resource: "" + identifier); var resourceType: seq<char> := info[0]; var value: seq<char> := Join(info[1..], ""/""); var resource: AwsResource := AwsResource(resourceType, value); Need(ValidAwsKmsResource(resource), ""Malformed resource: "" + identifier); Success(resource)
  }

  lemma /*{:_induction identifier}*/ ParseAwsKmsResourcesCorrect(identifier: string)
    ensures ParseAwsKmsResources(identifier).Success? ==> ghost var info: seq<seq<char>> := Split(identifier, '/'); ghost var r: Result<AwsResource, seq<char>> := ParseAwsKmsResources(identifier); |info| > 1 && Join([r.value.resourceType, r.value.value], ""/"") == identifier
    ensures ParseAwsKmsResources(identifier).Success? ==> ghost var resourceType: seq<char> := Split(identifier, '/')[0]; ""key"" == resourceType || ""alias"" == resourceType
    ensures ParseAwsKmsResources(identifier).Success? ==> ghost var info: seq<seq<char>> := Split(identifier, '/'); |Join(info[1..], ""/"")| > 0
    decreases identifier
  {
  }

  function method ParseAwsKmsArn(identifier: string): (result: Result<AwsKmsArn, string>)
    decreases identifier
  {
    var components: seq<seq<char>> := Split(identifier, ':');
    Need(6 == |components|, ""Malformed arn: "" + identifier); var resource: AwsKmsResource :- ParseAwsKmsResources(components[5]); var arn: AwsArn := AwsArn(components[0], components[1], components[2], components[3], components[4], resource); Need(ValidAwsKmsArn(arn), ""Malformed Arn:"" + identifier); Success(arn)
  }

  lemma /*{:_induction identifier}*/ ParseAwsKmsArnCorrect(identifier: string)
    ensures ParseAwsKmsArn(identifier).Success? ==> ""arn"" <= identifier
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')| == 6
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[1]| > 0
    ensures ParseAwsKmsArn(identifier).Success? ==> Split(identifier, ':')[2] == ""kms""
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[3]| > 0
    ensures ParseAwsKmsArn(identifier).Success? ==> |Split(identifier, ':')[4]| > 0
    decreases identifier
  {
  }

  function method ParseAwsKmsIdentifier(identifier: string): (result: Result<AwsKmsIdentifier, string>)
    decreases identifier
  {
    if ""arn:"" <= identifier then
      var arn: AwsKmsArn :- ParseAwsKmsArn(identifier); Success(AwsKmsArnIdentifier(arn))
    else
      var r: AwsKmsResource :- ParseAwsKmsRawResources(identifier); Success(AwsKmsRawResourceIdentifier(r))
  }

  predicate method IsMultiRegionAwsKmsArn(arn: AwsKmsArn)
    decreases arn
  {
    IsMultiRegionAwsKmsResource(arn.resource)
  }

  lemma IsMultiRegionAwsKmsArnCorrectness(arn: AwsKmsArn)
    ensures !IsMultiRegionAwsKmsArn(arn) <== arn.resource.resourceType == ""alias""
    ensures !IsMultiRegionAwsKmsArn(arn) <== arn.resource.resourceType == ""key"" && !(""mrk-"" <= arn.resource.value)
    ensures IsMultiRegionAwsKmsArn(arn) <== arn.resource.resourceType == ""key"" && ""mrk-"" <= arn.resource.value
    decreases arn
  {
  }

  predicate method IsMultiRegionAwsKmsIdentifier(identifier: AwsKmsIdentifier)
    decreases identifier
  {
    match identifier {
      case AwsKmsArnIdentifier(arn) =>
        IsMultiRegionAwsKmsArn(arn)
      case AwsKmsRawResourceIdentifier(r) =>
        IsMultiRegionAwsKmsResource(r)
    }
  }

  lemma IsMultiRegionAwsKmsIdentifierCorrect(s: string)
    ensures ""arn:"" <= s && ParseAwsKmsArn(s).Success? ==> ghost var arn: Result<AwsKmsArn, seq<char>> := ParseAwsKmsArn(s); ghost var arnIdentifier: AwsKmsIdentifier := AwsKmsArnIdentifier(arn.value); IsMultiRegionAwsKmsIdentifier(arnIdentifier) == IsMultiRegionAwsKmsArn(arn.value)
    ensures ""alias/"" <= s && ParseAwsKmsResources(s).Success? ==> ghost var resource: Result<AwsKmsResource, seq<char>> := ParseAwsKmsResources(s); ghost var resourceIdentifier: AwsKmsIdentifier := AwsKmsRawResourceIdentifier(resource.value); !IsMultiRegionAwsKmsIdentifier(resourceIdentifier)
    ensures ""mrk-"" <= s && ParseAwsKmsResources(s).Success? ==> ghost var resource: Result<AwsKmsResource, seq<char>> := ParseAwsKmsResources(s); ghost var resourceIdentifier: AwsKmsIdentifier := AwsKmsRawResourceIdentifier(resource.value); IsMultiRegionAwsKmsIdentifier(resourceIdentifier)
    ensures !(""arn:"" <= s) && !(""alias/"" <= s) && !(""mrk-"" <= s) && ParseAwsKmsIdentifier(s).Success? ==> ghost var resourceIdentifier: Result<AwsKmsIdentifier, string> := ParseAwsKmsIdentifier(s); !IsMultiRegionAwsKmsIdentifier(resourceIdentifier.value)
    decreases s
  {
  }

  predicate method IsMultiRegionAwsKmsResource(resource: AwsKmsResource)
    decreases resource
  {
    resource.resourceType == ""key"" &&
    ""mrk-"" <= resource.value
  }

  function method GetRegion(identifier: AwsKmsIdentifier): (res: Option<string>)
    decreases identifier
  {
    match identifier {
      case AwsKmsArnIdentifier(a) =>
        Some(a.region)
      case AwsKmsRawResourceIdentifier(_v0) =>
        None()
    }
  }
}

module {:extern ""KMSUtils""} KMSUtils {

  import EncryptionContext = EncryptionContext

  import opened AmazonKeyManagementService = AmazonKeyManagementService

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened AwsKmsArnParsing = AwsKmsArnParsing

  import UTF8 = UTF8
  type CustomerMasterKey = AwsKmsIdentifierString

  type GrantTokens = s: seq<GrantToken>
    | 0 <= |s| <= MAX_GRANT_TOKENS

  type GrantToken = s: string
    | 0 < |s| <= 8192
    witness *

  datatype ResponseMetadata = ResponseMetadata(metadata: map<string, string>, requestID: string)

  type HttpStatusCode = int

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>, keyID: AwsKmsIdentifierString, numberOfBytes: int32) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS &&
      0 < numberOfBytes <= 1024
    }
  }

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(ciphertextBlob: seq<uint8>, keyID: string, plaintext: seq<uint8>) {
    predicate method IsWellFormed()
      decreases this
    {
      |keyID| < UINT16_LIMIT &&
      |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype EncryptRequest = EncryptRequest(encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>, keyID: AwsKmsIdentifierString, plaintext: seq<uint8>) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype EncryptResponse = EncryptResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, responseMetadata: ResponseMetadata) {
    predicate method IsWellFormed()
      decreases this
    {
      |keyID| < UINT16_LIMIT &&
      |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype DecryptRequest = DecryptRequest(keyId: string, ciphertextBlob: seq<uint8>, encryptionContext: EncryptionContext.Map, grantTokens: seq<GrantToken>) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype DecryptResponse = DecryptResponse(contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)

  trait {:extern ""DafnyAWSKMSClientSupplier""} DafnyAWSKMSClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)
      decreases region
  }

  class BaseClientSupplier extends DafnyAWSKMSClientSupplier {
    constructor ()
    {
    }

    method GetClient(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)
      decreases region
    {
      var resClient := GetDefaultAWSKMSServiceClientExtern(region);
      return resClient;
    }
  }

  const MAX_GRANT_TOKENS := 10

  method {:extern ""KMSUtils.ClientHelper"", ""GetDefaultAWSKMSServiceClientExtern""} GetDefaultAWSKMSServiceClientExtern(region: Option<string>) returns (res: Result<IAmazonKeyManagementService, string>)
    decreases region

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyCalledWith(client: IAmazonKeyManagementService, request: GenerateDataKeyRequest)
    decreases client, request
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} GenerateDataKeyResult(ciphertextBlob: seq<uint8>, plaintext: seq<uint8>)
    decreases ciphertextBlob, plaintext
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EncryptCalledWith(client: IAmazonKeyManagementService, request: EncryptRequest)
    decreases client, request
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} EncryptResult(ciphertextBlob: seq<uint8>)
    decreases ciphertextBlob
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DecryptCalledWith(client: IAmazonKeyManagementService, request: DecryptRequest)
    decreases client, request
  {
    true
  }

  predicate {:opaque} {:fuel 0, 0} DecryptResult(keyID: string, plaintext: seq<uint8>)
    decreases keyID, plaintext
  {
    true
  }

  method {:extern ""KMSUtils.ClientHelper"", ""GenerateDataKey""} GenerateDataKey(client: IAmazonKeyManagementService, request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse, string>)
    requires request.Valid()
    ensures GenerateDataKeyCalledWith(client, request)
    ensures res.Success? ==> var r: GenerateDataKeyResponse := res.value; GenerateDataKeyResult(r.ciphertextBlob, r.plaintext)
    decreases client, request

  method {:extern ""KMSUtils.ClientHelper"", ""Encrypt""} Encrypt(client: IAmazonKeyManagementService, request: EncryptRequest) returns (res: Result<EncryptResponse, string>)
    requires request.Valid()
    ensures EncryptCalledWith(client, request)
    ensures res.Success? ==> EncryptResult(res.value.ciphertextBlob)
    decreases client, request

  method {:extern ""KMSUtils.ClientHelper"", ""Decrypt""} Decrypt(client: IAmazonKeyManagementService, request: DecryptRequest) returns (res: Result<DecryptResponse, string>)
    requires request.Valid()
    ensures DecryptCalledWith(client, request)
    ensures res.Success? ==> var r: DecryptResponse := res.value; DecryptResult(r.keyID, r.plaintext)
    decreases client, request
}

module {:extern ""AlgorithmSuite""} AlgorithmSuite {

  import opened Wrappers = Wrappers

  import Crypto = Aws.Crypto

  import opened UInt = StandardLibrary.UInt

  import EncryptionSuites = EncryptionSuites

  import S = Signature

  import KeyDerivationAlgorithms = KeyDerivationAlgorithms
  newtype ID = x: uint16
    | x in VALID_IDS
    witness 20
{
    function method EncryptionSuite(): EncryptionSuites.EncryptionSuite
      ensures EncryptionSuite().Valid()
      decreases this
    {
      Suite[this].algorithm
    }

    function method KeyLength(): nat
      decreases this
    {
      Suite[this].algorithm.keyLen as nat
    }

    predicate method ContainsIdentityKDF()
      decreases this
    {
      Suite[this].hkdf == KeyDerivationAlgorithms.IDENTITY
    }

    function method KDFInputKeyLength(): nat
      ensures ContainsIdentityKDF() ==> KDFInputKeyLength() == KeyLength()
      decreases this
    {
      match Suite[this].hkdf
      case HKDF_WITH_SHA_384() =>
        Suite[this].algorithm.keyLen as nat
      case HKDF_WITH_SHA_256() =>
        Suite[this].algorithm.keyLen as nat
      case IDENTITY() =>
        Suite[this].algorithm.keyLen as nat
    }

    function method IVLength(): nat
      decreases this
    {
      Suite[this].algorithm.ivLen as nat
    }

    function method TagLength(): nat
      decreases this
    {
      Suite[this].algorithm.tagLen as nat
    }

    function method SignatureType(): Option<S.ECDSAParams>
      decreases this
    {
      Suite[this].sign
    }

    predicate method ValidPlaintextDataKey(plaintextDataKey: seq<uint8>)
      decreases this, plaintextDataKey
    {
      |plaintextDataKey| == KDFInputKeyLength()
    }
  }

  datatype AlgSuite = AlgSuite(algorithm: EncryptionSuites.EncryptionSuite, hkdf: KeyDerivationAlgorithms.KeyDerivationAlgorithm, sign: Option<S.ECDSAParams>)

  const VALID_IDS: set<uint16> := {888, 838, 532, 376, 326, 276, 120, 70, 20}
  const AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 888
  const AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 838
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: ID := 532
  const AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG: ID := 376
  const AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG: ID := 326
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG: ID := 276
  const AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG: ID := 120
  const AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG: ID := 70
  const AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG: ID := 20
  const Suite := map[AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_256, KeyDerivationAlgorithms.HKDF_WITH_SHA_384, Some(S.ECDSA_P384)), AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_192, KeyDerivationAlgorithms.HKDF_WITH_SHA_384, Some(S.ECDSA_P384)), AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := AlgSuite(EncryptionSuites.AES_GCM_128, KeyDerivationAlgorithms.HKDF_WITH_SHA_256, Some(S.ECDSA_P256)), AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_256, KeyDerivationAlgorithms.HKDF_WITH_SHA_256, None), AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_192, KeyDerivationAlgorithms.HKDF_WITH_SHA_256, None), AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_128, KeyDerivationAlgorithms.HKDF_WITH_SHA_256, None), AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_256, KeyDerivationAlgorithms.IDENTITY, None), AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_192, KeyDerivationAlgorithms.IDENTITY, None), AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG := AlgSuite(EncryptionSuites.AES_GCM_128, KeyDerivationAlgorithms.IDENTITY, None)]

  function method PolymorphIDToInternalID(input: Crypto.AlgorithmSuiteId): (res: ID)
    decreases input
  {
    if input == Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF then
      AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF then
      AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF then
      AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256 then
      AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256 then
      AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256 then
      AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG
    else if input == Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 then
      AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
    else if input == Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 then
      AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
    else
      AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
  }

  function method InternalIDToPolymorphID(input: ID): (res: Crypto.AlgorithmSuiteId)
    decreases input
  {
    if input == AES_128_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_128_GCM_IV12_TAG16_NO_KDF
    else if input == AES_192_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_192_GCM_IV12_TAG16_NO_KDF
    else if input == AES_256_GCM_IV12_TAG16_IDENTITY_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_256_GCM_IV12_TAG16_NO_KDF
    else if input == AES_128_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256
    else if input == AES_192_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256
    else if input == AES_256_GCM_IV12_TAG16_HKDF_SHA256_NO_SIGNATURE_ALG then
      Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256
    else if input == AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 then
      Crypto.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256
    else if input == AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 then
      Crypto.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
    else
      Crypto.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
  }

  lemma SuiteIsComplete(id: ID)
    ensures id in Suite.Keys
    decreases id
  {
  }

  lemma ValidIDsAreSuiteKeys()
    ensures VALID_IDS == set id: ID {:trigger id in Suite.Keys} | id in Suite.Keys :: id as uint16
  {
    forall x: uint16 | x in VALID_IDS
      ensures exists id: ID :: id in Suite.Keys && id as uint16 == x
    {
      assert x as ID in Suite.Keys;
    }
  }
}

module {:extern ""Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient""} AwsCryptographicMaterialProviders {

  import opened Wrappers = Wrappers

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import EncryptionSuites = EncryptionSuites

  import UTF8 = UTF8

  import Crypto = Aws.Crypto

  import DefaultCMMDef = DefaultCMMDef

  import RawAESKeyringDef = RawAESKeyringDef

  import Esdk = Aws.Esdk
  class AwsCryptographicMaterialProvidersClient extends Crypto.IAwsCryptographicMaterialsProviderClient {
    constructor ()
    {
    }

    method CreateRawAesKeyring(input: Crypto.CreateRawAesKeyringInput) returns (res: Crypto.IKeyring)
      requires input.Valid()
      decreases input
    {
      var wrappingAlg: EncryptionSuites.EncryptionSuite;
      if input.wrappingAlg == Crypto.ALG_AES128_GCM_IV12_TAG16 {
        wrappingAlg := EncryptionSuites.AES_GCM_128;
      } else if input.wrappingAlg == Crypto.ALG_AES192_GCM_IV12_TAG16 {
        wrappingAlg := EncryptionSuites.AES_GCM_192;
      } else {
        assert input.wrappingAlg == Crypto.ALG_AES256_GCM_IV12_TAG16;
        wrappingAlg := EncryptionSuites.AES_GCM_256;
      }
      var namespaceRes := UTF8.Encode(input.keyNamespace);
      var namespace;
      if namespaceRes.Success? {
        namespace := namespaceRes.value;
      }
      var nameRes := UTF8.Encode(input.keyName);
      var name;
      if nameRes.Success? {
        name := nameRes.value;
      }
      assert wrappingAlg.Valid();
      expect |namespace| < UINT16_LIMIT, ""expectation violation""
      expect |input.wrappingKey| == 16 || |input.wrappingKey| == 24 || |input.wrappingKey| == 32, ""expectation violation""
      expect |input.wrappingKey| == wrappingAlg.keyLen as int, ""expectation violation""
      return new RawAESKeyringDef.RawAESKeyring(namespace, name, input.wrappingKey, wrappingAlg);
    }

    method CreateDefaultCryptographicMaterialsManager(input: Crypto.CreateDefaultCryptographicMaterialsManagerInput) returns (res: Crypto.ICryptographicMaterialsManager)
      requires input.Valid()
      decreases input
    {
      return new DefaultCMMDef.DefaultCMM.OfKeyring(input.keyring);
    }
  }
}

module {:extern ""Dafny.Aws.Esdk.AwsEncryptionSdkClient""} AwsEncryptionSdk {

  import opened Wrappers = Wrappers

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import Crypto = Aws.Crypto

  import Esdk = Aws.Esdk

  import EncryptDecrypt = EncryptDecrypt
  class AwsEncryptionSdkClient extends Esdk.IAwsEncryptionSdkClient {
    constructor ()
    {
    }

    method Encrypt(input: Esdk.EncryptInput) returns (res: Result<Esdk.EncryptOutput, string>)
      requires input.Valid()
      decreases input
    {
      var encryptRequest := EncryptDecrypt.EncryptRequest.WithCMM(input.plaintext, input.materialsManager).SetEncryptionContext(input.encryptionContext);
      var e :- EncryptDecrypt.Encrypt(encryptRequest);
      return Success(Esdk.EncryptOutput(ciphertext := e));
    }

    method Decrypt(input: Esdk.DecryptInput) returns (res: Result<Esdk.DecryptOutput, string>)
      requires input.Valid()
      decreases input
    {
      var decryptRequest := EncryptDecrypt.DecryptRequest.WithCMM(input.ciphertext, input.materialsManager);
      var d :- EncryptDecrypt.Decrypt(decryptRequest);
      return Success(Esdk.DecryptOutput(plaintext := d));
    }
  }
}

module {:extern ""DefaultCMMDef""} DefaultCMMDef {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import EncryptionContext = EncryptionContext

  import AlgorithmSuite = AlgorithmSuite

  import Signature = Signature

  import Base64 = Base64

  import MessageHeader = MessageHeader

  import UTF8 = UTF8

  import Deserialize = Deserialize

  import Crypto = Aws.Crypto
  class DefaultCMM extends Crypto.ICryptographicMaterialsManager {
    const keyring: Crypto.IKeyring

    constructor OfKeyring(k: Crypto.IKeyring)
      ensures keyring == k
      decreases k
    {
      keyring := k;
    }

    method GetEncryptionMaterials(input: Crypto.GetEncryptionMaterialsInput) returns (res: Result<Crypto.GetEncryptionMaterialsOutput, string>)
      requires input.Valid()
      ensures res.Success? ==> res.value.encryptionMaterials.plaintextDataKey.Some? && Serializable(res.value.encryptionMaterials)
      ensures Materials.EC_PUBLIC_KEY_FIELD in input.encryptionContext ==> res.Failure?
      ensures res.Success? && (input.algorithmSuiteId.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value).SignatureType().Some?) ==> Materials.EC_PUBLIC_KEY_FIELD in res.value.encryptionMaterials.encryptionContext
      ensures res.Success? ==> Serializable(res.value.encryptionMaterials)
      ensures res.Success? ==> match input.algorithmSuiteId { case None => AlgorithmSuite.PolymorphIDToInternalID(res.value.encryptionMaterials.algorithmSuiteId) == 888 case Some(_mcc#0) => var id := _mcc#0; res.value.encryptionMaterials.algorithmSuiteId == id }
      decreases input
    {
      var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
      assert reservedField in Materials.RESERVED_KEY_VALUES;
      if reservedField in input.encryptionContext.Keys {
        return Failure(""Reserved Field found in EncryptionContext keys."");
      }
      var id := AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      if input.algorithmSuiteId.Some? {
        id := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value);
      }
      var enc_sk := None;
      var enc_ctx := input.encryptionContext;
      match id.SignatureType() {
        case {:split false} None() =>
        case {:split false} Some(param) =>
          var signatureKeys :- Signature.KeyGen(param);
          enc_sk := Some(signatureKeys.signingKey);
          var enc_vk :- UTF8.Encode(Base64.Encode(signatureKeys.verificationKey));
          enc_ctx := enc_ctx[reservedField := enc_vk];
      }
      var validAAD := EncryptionContext.CheckSerializable(enc_ctx);
      if !validAAD {
        return Failure(""Invalid Encryption Context"");
      }
      assert EncryptionContext.Serializable(enc_ctx);
      var materials := Crypto.EncryptionMaterials(encryptionContext := enc_ctx, algorithmSuiteId := AlgorithmSuite.InternalIDToPolymorphID(id), plaintextDataKey := None(), encryptedDataKeys := [], signingKey := enc_sk);
      assert materials.encryptionContext == enc_ctx;
      var result :- keyring.OnEncrypt(Crypto.OnEncryptInput(materials := materials));
      if result.materials.plaintextDataKey.None? || |result.materials.encryptedDataKeys| == 0 {
        return Failure(""Could not retrieve materials required for encryption"");
      }
      assert result.materials.Valid();
      :- Need(OnEncryptResultValid(input, result), ""Keyring returned an invalid response"");
      return Success(Crypto.GetEncryptionMaterialsOutput(encryptionMaterials := result.materials));
    }

    method DecryptMaterials(input: Crypto.DecryptMaterialsInput) returns (res: Result<Crypto.DecryptMaterialsOutput, string>)
      requires input.Valid()
      ensures res.Success? ==> res.value.decryptionMaterials.plaintextDataKey.Some?
      decreases input
    {
      var vkey := None;
      var algID := AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId);
      var encCtx := input.encryptionContext;
      if algID.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        if reservedField !in encCtx {
          return Failure(""Could not get materials required for decryption."");
        }
        var encodedVKey := encCtx[reservedField];
        var utf8Decoded :- UTF8.Decode(encodedVKey);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }
      var materials := Crypto.DecryptionMaterials(encryptionContext := encCtx, algorithmSuiteId := input.algorithmSuiteId, plaintextDataKey := None(), verificationKey := vkey);
      var result :- keyring.OnDecrypt(Crypto.OnDecryptInput(materials := materials, encryptedDataKeys := input.encryptedDataKeys));
      if result.materials.plaintextDataKey.None? {
        return Failure(""Keyring.OnDecrypt failed to decrypt the plaintext data key."");
      }
      return Success(Crypto.DecryptMaterialsOutput(decryptionMaterials := result.materials));
    }

    predicate method OnEncryptResultValid(input: Crypto.GetEncryptionMaterialsInput, result: Crypto.OnEncryptOutput)
      decreases input, result
    {
      result.materials.plaintextDataKey.Some? &&
      Serializable(result.materials) &&
      (input.algorithmSuiteId.None? || AlgorithmSuite.PolymorphIDToInternalID(input.algorithmSuiteId.value).SignatureType().Some? ==>
        Materials.EC_PUBLIC_KEY_FIELD in result.materials.encryptionContext) &&
      match input.algorithmSuiteId { case None => AlgorithmSuite.PolymorphIDToInternalID(result.materials.algorithmSuiteId) == 888 case Some(_mcc#0) => var id := _mcc#0; result.materials.algorithmSuiteId == id }
    }
  }

  predicate method Serializable(mat: Crypto.EncryptionMaterials)
    decreases mat
  {
    |mat.encryptedDataKeys| > 0 &&
    EncryptionContext.Serializable(mat.encryptionContext)
  }
}

module Deserialize {

  export
    provides DeserializeHeader, Materials, Streams, StandardLibrary, Wrappers, UInt, AlgorithmSuite, Msg, InsertNewEntry, UTF8, EncryptionContext
    reveals DeserializeHeaderResult


  import Crypto = Aws.Crypto

  import Msg = MessageHeader

  import AlgorithmSuite = AlgorithmSuite

  import Streams = Streams

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import Materials = Materials

  import EncryptionContext = EncryptionContext
  datatype DeserializeHeaderResult = DeserializeHeaderResult(header: Msg.Header, ghost hbSeq: seq<uint8>)

  method DeserializeHeader(rd: Streams.ByteReader) returns (res: Result<DeserializeHeaderResult, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res { case Success(_mcc#0) => (var desres := _mcc#0; desres.header.Valid() && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| && Msg.IsSerializationOfHeaderBody(desres.hbSeq, desres.header.body) && desres.hbSeq + desres.header.auth.iv + desres.header.auth.authenticationTag == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var hb :- DeserializeHeaderBody(rd);
    ghost var hbSeq := rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
    var auth :- DeserializeHeaderAuthentication(rd, hb.algorithmSuiteID);
    return Success(DeserializeHeaderResult(Msg.Header(hb, auth), hbSeq));
  }

  method DeserializeHeaderBody(rd: Streams.ByteReader) returns (ret: Result<Msg.HeaderBody, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var hb := _mcc#0; hb.Valid() && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| && Msg.IsSerializationOfHeaderBody(rd.reader.data[old(rd.reader.pos) .. rd.reader.pos], hb)) case Failure(_mcc#1) => true }
    decreases rd
  {
    var version :- DeserializeVersion(rd);
    var typ :- DeserializeType(rd);
    var algorithmSuiteID :- DeserializeAlgorithmSuiteID(rd);
    var messageID :- DeserializeMsgID(rd);
    ghost var aadStart := rd.reader.pos;
    var aad :- DeserializeAAD(rd);
    ghost var aadEnd := rd.reader.pos;
    var encryptedDataKeys :- DeserializeEncryptedDataKeys(rd);
    var contentType :- DeserializeContentType(rd);
    ghost var reserveStart := rd.reader.pos;
    var _ :- DeserializeReserved(rd);
    ghost var reserveEnd := rd.reader.pos;
    assert [version as uint8] + [typ as uint8] + UInt16ToSeq(algorithmSuiteID as uint16) + messageID + rd.reader.data[aadStart .. aadEnd] + Msg.EDKsToSeq(encryptedDataKeys) + [Msg.ContentTypeToUInt8(contentType)] + rd.reader.data[reserveStart .. reserveEnd] == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
    assert [version as uint8] + [typ as uint8] + UInt16ToSeq(algorithmSuiteID as uint16) + messageID + rd.reader.data[aadStart .. aadEnd] + Msg.EDKsToSeq(encryptedDataKeys) + [Msg.ContentTypeToUInt8(contentType)] + [0, 0, 0, 0] == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
    var ivLength :- rd.ReadByte();
    var frameLength :- rd.ReadUInt32();
    assert [version as uint8] + [typ as uint8] + UInt16ToSeq(algorithmSuiteID as uint16) + messageID + rd.reader.data[aadStart .. aadEnd] + Msg.EDKsToSeq(encryptedDataKeys) + [Msg.ContentTypeToUInt8(contentType)] + [0, 0, 0, 0] + [ivLength] + UInt32ToSeq(frameLength) == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
    if ivLength as nat != algorithmSuiteID.IVLength() {
      return Failure(""Deserialization Error: Incorrect IV length."");
    }
    if contentType.NonFramed? && frameLength != 0 {
      return Failure(""Deserialization Error: Frame length must be 0 when content type is non-framed."");
    } else if contentType.Framed? && frameLength == 0 {
      return Failure(""Deserialization Error: Frame length must be non-0 when content type is framed."");
    }
    reveal Msg.IsSerializationOfHeaderBody();
    var hb := Msg.HeaderBody(version, typ, algorithmSuiteID, messageID, aad, encryptedDataKeys, contentType, ivLength, frameLength);
    assert Msg.IsSerializationOfHeaderBody(rd.reader.data[old(rd.reader.pos) .. rd.reader.pos], hb) by {
      reveal Msg.IsSerializationOfHeaderBody();
      ghost var s := rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
      ghost var serializedAAD := rd.reader.data[aadStart .. aadEnd];
      assert EncryptionContext.LinearSeqToMap(serializedAAD, aad);
      assert s[0 .. 1] == [hb.version as uint8];
      assert Msg.IsSerializationOfHeaderBodyAux(s, hb, serializedAAD);
    }
    return Success(hb);
  }

  method DeserializeHeaderAuthentication(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<Msg.HeaderAuthentication, string>)
    requires rd.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var ha := _mcc#0; var bytesRead := algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength(); var serHa := ha.iv + ha.authenticationTag; |ha.iv| == algorithmSuiteID.IVLength() && |ha.authenticationTag| == algorithmSuiteID.TagLength() && old(rd.reader.pos) + bytesRead == rd.reader.pos && serHa == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd, algorithmSuiteID
  {
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    var authenticationTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    return Success(Msg.HeaderAuthentication(iv, authenticationTag));
  }

  method DeserializeVersion(rd: Streams.ByteReader) returns (ret: Result<Msg.Version, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var ver := _mcc#0; var bytesRead := 1; var serVer := [ver as uint8]; old(rd.reader.pos) + bytesRead == rd.reader.pos && serVer == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var version :- rd.ReadByte();
    if version == Msg.VERSION_1 {
      return Success(version);
    } else {
      return Failure(""Deserialization Error: Version not supported."");
    }
  }

  method DeserializeType(rd: Streams.ByteReader) returns (ret: Result<Msg.Type, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var typ := _mcc#0; var bytesRead := 1; var serTyp := [typ as uint8]; old(rd.reader.pos) + bytesRead == rd.reader.pos && serTyp == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var typ :- rd.ReadByte();
    if typ == Msg.TYPE_CUSTOMER_AED {
      return Success(typ);
    } else {
      return Failure(""Deserialization Error: Type not supported."");
    }
  }

  method DeserializeAlgorithmSuiteID(rd: Streams.ByteReader) returns (ret: Result<AlgorithmSuite.ID, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var algID := _mcc#0; var bytesRead := 2; var serAlgID := UInt16ToSeq(algID as uint16); old(rd.reader.pos) + bytesRead == rd.reader.pos && serAlgID == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var algorithmSuiteID :- rd.ReadUInt16();
    if algorithmSuiteID in AlgorithmSuite.VALID_IDS {
      return Success(algorithmSuiteID as AlgorithmSuite.ID);
    } else {
      return Failure(""Deserialization Error: Algorithm suite not supported."");
    }
  }

  method DeserializeMsgID(rd: Streams.ByteReader) returns (ret: Result<Msg.MessageID, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var messageID := _mcc#0; var bytesRead := |messageID|; var sermessageID := messageID; old(rd.reader.pos) + bytesRead == rd.reader.pos && sermessageID == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var msgID: seq<uint8> :- rd.ReadBytes(Msg.MESSAGE_ID_LEN);
    return Success(msgID);
  }

  method DeserializeUTF8(rd: Streams.ByteReader, n: nat) returns (ret: Result<UTF8.ValidUTF8Bytes, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures ret.Success? ==> var expectedRes: Option<UTF8.ValidUTF8Bytes> := EncryptionContext.GetUTF8(rd.reader.data[old(rd.reader.pos)..], n); expectedRes.Some? && expectedRes.value == ret.value
    ensures match ret { case Success(_mcc#0) => (var bytes := _mcc#0; UTF8.ValidUTF8Seq(bytes) && old(rd.reader.pos) + n == rd.reader.pos && bytes == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd, n
  {
    var bytes :- rd.ReadBytes(n);
    if UTF8.ValidUTF8Seq(bytes) {
      var utf8: UTF8.ValidUTF8Bytes := bytes;
      assert bytes == rd.reader.data[old(rd.reader.pos)..][..n];
      return Success(utf8);
    } else {
      return Failure(""Deserialization Error: Not a valid UTF8 string."");
    }
  }

  method DeserializeAAD(rd: Streams.ByteReader) returns (ret: Result<EncryptionContext.Map, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var aad := _mcc#0; EncryptionContext.Serializable(aad) && old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| && EncryptionContext.LinearSeqToMap(rd.reader.data[old(rd.reader.pos) .. rd.reader.pos], aad)) case Failure(_mcc#1) => true }
    decreases rd
  {
    reveal EncryptionContext.Serializable();
    var kvPairsLength :- rd.ReadUInt16();
    if kvPairsLength == 0 {
      return Success(map[]);
    } else if kvPairsLength < 2 {
      return Failure(""Deserialization Error: The number of bytes in encryption context exceeds the given length."");
    }
    var totalBytesRead := 0;
    var kvPairsCount :- rd.ReadUInt16();
    totalBytesRead := totalBytesRead + 2;
    if kvPairsCount == 0 {
      return Failure(""Deserialization Error: Key value pairs count is 0."");
    }
    var kvPairs: EncryptionContext.Linear := [];
    var i := 0;
    ghost var startKvPos := rd.reader.pos;
    ghost var unsortedKvPairs: EncryptionContext.Linear := [];
    while i < kvPairsCount
      invariant startKvPos <= rd.reader.pos
      invariant rd.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant |kvPairs| == |unsortedKvPairs|
      invariant forall kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: kvPair in kvPairs <==> kvPair in unsortedKvPairs
      invariant totalBytesRead == 2 + EncryptionContext.LinearLength(kvPairs, 0, i as nat) <= kvPairsLength as nat
      invariant totalBytesRead == |rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]| - 2
      invariant EncryptionContext.SerializableLinear(kvPairs)
      invariant EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs)
      invariant rd.reader.data[startKvPos .. rd.reader.pos] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|)
      decreases kvPairsCount as int - i as int
    {
      ghost var oldPosPair := rd.reader.pos;
      ghost var oldKvPairs := kvPairs;
      ghost var oldunsortedKvPairs := unsortedKvPairs;
      var keyLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      var key :- DeserializeUTF8(rd, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;
      var valueLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      if kvPairsLength as nat < totalBytesRead + valueLength as nat {
        return Failure(""Deserialization Error: The number of bytes in encryption context exceeds the given length."");
      }
      var value :- DeserializeUTF8(rd, valueLength as nat);
      totalBytesRead := totalBytesRead + |value|;
      var opt, insertionPoint := InsertNewEntry(kvPairs, key, value);
      match opt {
        case {:split false} Some(kvPairs_) =>
          EncryptionContext.LinearInsert(kvPairs, insertionPoint, key, value);
          kvPairs := kvPairs_;
          unsortedKvPairs := unsortedKvPairs + [(key, value)];
        case {:split false} None() =>
          return Failure(""Deserialization Error: Duplicate key."");
      }
      i := i + 1;
      assert EncryptionContext.KVPairToSeq((key, value)) == rd.reader.data[oldPosPair .. rd.reader.pos] by {
        assert rd.reader.data[oldPosPair .. rd.reader.pos] == rd.reader.data[oldPosPair .. oldPosPair + 4 + |key| + |value|];
        assert UInt16ToSeq(|key| as uint16) == rd.reader.data[oldPosPair .. oldPosPair + 2];
        assert key == rd.reader.data[oldPosPair + 2 .. oldPosPair + 2 + |key|];
        assert UInt16ToSeq(|value| as uint16) == rd.reader.data[oldPosPair + 2 + |key| .. oldPosPair + 2 + |key| + 2];
        assert value == rd.reader.data[oldPosPair + 4 + |key| .. oldPosPair + 4 + |key| + |value|];
      }
      assert forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in oldKvPairs || p == (key, value) <==> p in kvPairs;
      assert rd.reader.data[startKvPos .. rd.reader.pos] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) by {
        EncryptionContext.LinearToUnorderedSeqInductiveStep(oldunsortedKvPairs, [(key, value)], 0, |oldunsortedKvPairs|);
        assert EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs| - 1) == rd.reader.data[startKvPos .. oldPosPair];
        assert EncryptionContext.KVPairToSeq(unsortedKvPairs[|unsortedKvPairs| - 1]) == rd.reader.data[oldPosPair .. rd.reader.pos];
        assert rd.reader.data[startKvPos .. rd.reader.pos] == rd.reader.data[startKvPos .. oldPosPair] + rd.reader.data[oldPosPair .. rd.reader.pos];
      }
    }
    if kvPairsLength as nat != totalBytesRead {
      return Failure(""Deserialization Error: Bytes actually read differs from bytes supposed to be read."");
    }
    var encryptionContext: map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes> := EncryptionContext.LinearToMap(kvPairs);
    var isValid := EncryptionContext.CheckSerializable(encryptionContext);
    if !isValid || |kvPairs| != |encryptionContext| {
      return Failure(""Deserialization Error: Failed to parse encryption context."");
    }
    SerializationIsValid(rd.reader.data[old(rd.reader.pos) .. rd.reader.pos], encryptionContext, unsortedKvPairs, kvPairs);
    return Success(encryptionContext);
  }

  lemma /*{:_induction unsortedKvPairs, kvPairs}*/ SerializationIsValid(sequence: seq<uint8>, resultMap: EncryptionContext.Map, unsortedKvPairs: EncryptionContext.Linear, kvPairs: EncryptionContext.Linear)
    requires |resultMap| == 0 ==> |sequence| == 2
    requires |resultMap| != 0 ==> 4 <= |sequence|
    requires EncryptionContext.Serializable(resultMap)
    requires |resultMap| == |kvPairs| == |unsortedKvPairs|
    requires forall kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: kvPair in kvPairs <==> kvPair in unsortedKvPairs
    requires EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs)
    requires EncryptionContext.SerializableLinear(kvPairs)
    requires (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(resultMap) && EncryptionContext.SerializableLinear(kvPairs) ==> EncryptionContext.MapToSeq(resultMap) == if |resultMap| == 0 then [] else UInt16ToSeq(|kvPairs| as uint16) + EncryptionContext.LinearToSeq(kvPairs, 0, |kvPairs|))
    requires |sequence[2..]| < UINT16_LIMIT && sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16)
    requires |resultMap| != 0 ==> sequence[2..][..2] == UInt16ToSeq(|resultMap| as uint16)
    requires |resultMap| != 0 ==> sequence[4..] == EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|)
    ensures EncryptionContext.LinearSeqToMap(sequence, resultMap)
    decreases sequence, resultMap, unsortedKvPairs, kvPairs
  {
    reveal EncryptionContext.Serializable();
    if |resultMap| == 0 {
    } else {
      assert EncryptionContext.LinearSeqToMap(sequence, resultMap) by {
        assert EncryptionContext.SeqToMap(sequence[2..], resultMap) by {
          EncryptionContext.InsertionSortPreservesProperties(unsortedKvPairs);
          EncryptionContext.SortedSequenceIsUnqiue(kvPairs, EncryptionContext.InsertionSort(unsortedKvPairs));
          assert EncryptionContext.SeqToLinearToMap(sequence[2..], resultMap, unsortedKvPairs, kvPairs) by {
            assert 2 <= |sequence[2..]|;
            assert EncryptionContext.SerializableUnsortedLinear(unsortedKvPairs);
            assert EncryptionContext.SerializableLinear(kvPairs);
            assert EncryptionContext.SerializableKVPairs(resultMap);
            assert sequence[2..][..2] == UInt16ToSeq(|resultMap| as uint16);
            assert EncryptionContext.LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) == sequence[2..][2..];
            assert kvPairs == EncryptionContext.InsertionSort(unsortedKvPairs);
            assert EncryptionContext.MapToSeq(resultMap) == sequence[2..][..2] + EncryptionContext.LinearToSeq(kvPairs, 0, |kvPairs|);
          }
          assert sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16);
        }
      }
    }
  }

  method InsertNewEntry(kvPairs: EncryptionContext.Linear, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
      returns (res: Option<EncryptionContext.Linear>, ghost insertionPoint: nat)
    requires EncryptionContext.LinearSorted(kvPairs)
    requires forall i: int, j: int | 0 <= i < j < |kvPairs| :: kvPairs[i].0 != kvPairs[j].0
    ensures (exists l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | l in kvPairs :: key == l.0) <==> res.None?
    ensures match res { case None => (exists i :: 0 <= i < |kvPairs| && kvPairs[i].0 == key) case Some(_mcc#0) => var kvPairs' := _mcc#0; insertionPoint <= |kvPairs| && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..] && EncryptionContext.LinearSorted(kvPairs') && forall i, j | 0 <= i < j < |kvPairs'| :: kvPairs'[i].0 != kvPairs'[j].0 }
    decreases kvPairs, key, value
  {
    var n := |kvPairs|;
    while 0 < n && LexicographicLessOrEqual(key, kvPairs[n - 1].0, UInt.UInt8Less)
      invariant 0 <= n <= |kvPairs|
      invariant forall i: int :: n <= i < |kvPairs| ==> LexicographicLessOrEqual(key, kvPairs[i].0, UInt.UInt8Less)
      invariant forall i: int | n < i < |kvPairs| :: kvPairs[i].0 != key
      decreases n - 0
    {
      n := n - 1;
    }
    EncryptionContext.LinearSortedImpliesStrongLinearSorted(kvPairs);
    if kvPairs != [] && LexicographicLessOrEqual(key, kvPairs[|kvPairs| - 1].0, UInt.UInt8Less) && kvPairs[n].0 == key {
      return None, n;
    } else {
      var kvPairs' := kvPairs[..n] + [(key, value)] + kvPairs[n..];
      if 0 < n {
        LexIsTotal(kvPairs'[n - 1].0, kvPairs'[n].0, UInt.UInt8Less);
      }
      return Some(kvPairs'), n;
    }
  }

  method DeserializeEncryptedDataKeys(rd: Streams.ByteReader) returns (ret: Result<Msg.EncryptedDataKeys, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var edks := _mcc#0; edks.Valid() && var n := |Msg.EDKsToSeq(edks)|; old(rd.reader.pos) + n == rd.reader.pos && Msg.EDKsToSeq(edks) == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var edkCount :- rd.ReadUInt16();
    if edkCount == 0 {
      return Failure(""Deserialization Error: Encrypted data key count is 0."");
    }
    assert rd.reader.pos == old(rd.reader.pos) + 2;
    var edkEntries: seq<Crypto.EncryptedDataKey> := [];
    var i := 0;
    while i < edkCount
      invariant old(rd.reader.pos) + 2 <= rd.reader.pos
      invariant rd.Valid()
      invariant i <= edkCount
      invariant |edkEntries| == i as int
      invariant forall i: int :: 0 <= i < |edkEntries| ==> edkEntries[i].Valid()
      invariant Msg.EDKEntriesToSeq(edkEntries, 0, |edkEntries|) == rd.reader.data[old(rd.reader.pos) + 2 .. rd.reader.pos]
      decreases edkCount as int - i as int
    {
      ghost var edkStartPos := rd.reader.pos;
      ghost var providerIdStartPos := edkStartPos;
      var providerIdLength :- rd.ReadUInt16();
      var str :- DeserializeUTF8(rd, providerIdLength as nat);
      var providerId := str;
      assert rd.reader.pos == providerIdStartPos + 2 + |providerId|;
      assert UInt16ToSeq(|providerId| as uint16) + providerId == rd.reader.data[providerIdStartPos .. rd.reader.pos];
      ghost var providerInfoStartPos := rd.reader.pos;
      var providerInfoLength :- rd.ReadUInt16();
      var providerInfo :- rd.ReadBytes(providerInfoLength as nat);
      assert rd.reader.pos == providerInfoStartPos + 2 + |providerInfo|;
      assert UInt16ToSeq(|providerInfo| as uint16) + providerInfo == rd.reader.data[providerInfoStartPos .. rd.reader.pos];
      ghost var ciphertextStartPos := rd.reader.pos;
      var ciphertextLength :- rd.ReadUInt16();
      var ciphertext :- rd.ReadBytes(ciphertextLength as nat);
      assert rd.reader.pos == ciphertextStartPos + 2 + |ciphertext|;
      assert UInt16ToSeq(|ciphertext| as uint16) + ciphertext == rd.reader.data[ciphertextStartPos .. rd.reader.pos];
      edkEntries := edkEntries + [Crypto.EncryptedDataKey(keyProviderId := providerId, keyProviderInfo := providerInfo, ciphertext := ciphertext)];
      i := i + 1;
      assert edkStartPos + 2 + |providerId| + 2 + |providerInfo| + 2 + |ciphertext| == rd.reader.pos;
      assert Msg.EDKEntriesToSeq(edkEntries, 0, |edkEntries|) == rd.reader.data[old(rd.reader.pos) + 2 .. rd.reader.pos] by {
        assert UInt16ToSeq(|providerId| as uint16) + providerId == rd.reader.data[edkStartPos .. edkStartPos + 2 + |providerId|];
        assert UInt16ToSeq(|providerInfo| as uint16) + providerInfo == rd.reader.data[edkStartPos + 2 + |providerId| .. edkStartPos + 2 + |providerId| + 2 + |providerInfo|];
        assert Msg.EDKEntryToSeq(Crypto.EncryptedDataKey(keyProviderId := providerId, keyProviderInfo := providerInfo, ciphertext := ciphertext)) == rd.reader.data[edkStartPos .. rd.reader.pos];
        Msg.EDKEntriesToSeqInductiveStep(edkEntries[..|edkEntries| - 1], [Crypto.EncryptedDataKey(keyProviderId := providerId, keyProviderInfo := providerInfo, ciphertext := ciphertext)], 0, |edkEntries[..|edkEntries| - 1]|);
      }
    }
    assert |edkEntries| == edkCount as int;
    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(rd: Streams.ByteReader) returns (ret: Result<Msg.ContentType, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var contentType := _mcc#0; old(rd.reader.pos) + 1 == rd.reader.pos && [Msg.ContentTypeToUInt8(contentType)] == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var byte :- rd.ReadByte();
    match Msg.UInt8ToContentType(byte)
    case {:split false} None() =>
      return Failure(""Deserialization Error: Content type not supported."");
    case {:split false} Some(contentType) =>
      return Success(contentType);
  }

  method DeserializeReserved(rd: Streams.ByteReader) returns (ret: Result<seq<uint8>, string>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match ret { case Success(_mcc#0) => (var contnetType := _mcc#0; old(rd.reader.pos) + 4 == rd.reader.pos && Msg.Reserved == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd
  {
    var reserved :- rd.ReadBytes(4);
    if reserved == Msg.Reserved {
      return Success(reserved);
    } else {
      return Failure(""Deserialization Error: Reserved fields must be 0."");
    }
  }
}

module {:extern ""EncryptDecrypt""} EncryptDecrypt {

  import opened Wrappers = Wrappers

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Crypto = Aws.Crypto

  import EncryptionContext = EncryptionContext

  import AlgorithmSuite = AlgorithmSuite

  import AESEncryption = AESEncryption

  import DefaultCMMDef = DefaultCMMDef

  import Deserialize = Deserialize

  import HKDF = HKDF

  import KeyDerivationAlgorithms = KeyDerivationAlgorithms

  import Materials = Materials

  import Msg = MessageHeader

  import MessageBody = MessageBody

  import Random = Random

  import Serialize = Serialize

  import Signature = Signature

  import Streams = Streams
  datatype EncryptRequest = EncryptRequest(plaintext: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager?, keyring: Crypto.IKeyring?, plaintextLength: nat, encryptionContext: EncryptionContext.Map, algorithmSuiteID: Option<uint16>, frameLength: Option<uint32>) {
    static function method WithCMM(plaintext: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager): EncryptRequest
      decreases plaintext, cmm
    {
      EncryptRequest(plaintext, cmm, null, |plaintext|, map[], None, None)
    }

    static function method WithKeyring(plaintext: seq<uint8>, keyring: Crypto.IKeyring): EncryptRequest
      decreases plaintext, keyring
    {
      EncryptRequest(plaintext, null, keyring, |plaintext|, map[], None, None)
    }

    function method SetEncryptionContext(encryptionContext: EncryptionContext.Map): EncryptRequest
      decreases this, encryptionContext
    {
      this.(encryptionContext := encryptionContext)
    }

    function method SetAlgorithmSuiteID(algorithmSuiteID: uint16): EncryptRequest
      decreases this, algorithmSuiteID
    {
      this.(algorithmSuiteID := Some(algorithmSuiteID))
    }

    function method SetFrameLength(frameLength: uint32): EncryptRequest
      decreases this, frameLength
    {
      this.(frameLength := Some(frameLength))
    }
  }

  datatype DecryptRequest = DecryptRequest(message: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager?, keyring: Crypto.IKeyring?) {
    static function method WithCMM(message: seq<uint8>, cmm: Crypto.ICryptographicMaterialsManager): DecryptRequest
      decreases message, cmm
    {
      DecryptRequest(message, cmm, null)
    }

    static function method WithKeyring(message: seq<uint8>, keyring: Crypto.IKeyring): DecryptRequest
      decreases message, keyring
    {
      DecryptRequest(message, null, keyring)
    }
  }

  datatype DecryptResultWithVerificationInfo = DecryptResultWithVerificationInfo(plaintext: seq<uint8>, ghost header: Msg.Header, ghost hbSeq: seq<uint8>, ghost frames: seq<MessageBody.Frame>, ghost signature: Option<seq<uint8>>)

  const DEFAULT_FRAME_LENGTH: uint32 := 4096

  function SerializeMessageWithSignature(headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication, frames: seq<MessageBody.Frame>, signature: seq<uint8>): (message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
    requires |signature| < UINT16_LIMIT
    decreases headerBody, headerAuthentication, frames, signature
  {
    ghost var serializedSignature: seq<uint8> := UInt16ToSeq(|signature| as uint16) + signature;
    SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames) + serializedSignature
  }

  function SerializeMessageWithoutSignature(headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication, frames: seq<MessageBody.Frame>): (message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
    decreases headerBody, headerAuthentication, frames
  {
    ghost var serializedHeaderBody: seq<uint8> := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    ghost var serializedHeaderAuthentication: seq<uint8> := headerAuthentication.iv + headerAuthentication.authenticationTag;
    ghost var serializedFrames: seq<uint8> := MessageBody.FramesToSequence(frames);
    serializedHeaderBody + serializedHeaderAuthentication + serializedFrames
  }

  predicate ValidHeaderBodyForRequest(headerBody: Msg.HeaderBody, request: EncryptRequest)
    decreases headerBody, request
  {
    headerBody.Valid() &&
    headerBody.version == Msg.VERSION_1 &&
    headerBody.typ == Msg.TYPE_CUSTOMER_AED &&
    headerBody.contentType == Msg.ContentType.Framed &&
    headerBody.frameLength == if request.frameLength.Some? then request.frameLength.value else DEFAULT_FRAME_LENGTH
  }

  predicate ValidHeaderAuthenticationForRequest(headerAuthentication: Msg.HeaderAuthentication, headerBody: Msg.HeaderBody)
    requires headerBody.Valid()
    decreases headerAuthentication, headerBody
  {
    ghost var serializedHeaderBody: seq<uint8> := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), (_: int) => 0) &&
    Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody) &&
    exists encryptionOutput: AESEncryption.EncryptionOutput, cipherkey: seq<uint8> | IsDerivedKey(cipherkey) :: 
      AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, cipherkey)
  }

  predicate ValidFramesForRequest(frames: seq<MessageBody.Frame>, request: EncryptRequest, headerBody: Msg.HeaderBody)
    decreases frames, request, headerBody
  {
    (forall frame: MessageBody.Frame | frame in frames :: 
      frame.Valid()) &&
    MessageBody.FramesEncryptPlaintext(frames, request.plaintext) &&
    (forall frame: MessageBody.Frame | frame in frames :: 
      |frame.iv| == headerBody.algorithmSuiteID.IVLength()) &&
    exists cipherkey: seq<uint8> | IsDerivedKey(cipherkey) :: 
      forall frame: MessageBody.Frame | frame in frames :: 
        AESEncryption.EncryptedWithKey(frame.encContent, cipherkey)
  }

  predicate ValidSignatureForRequest(signature: seq<uint8>, headerBody: Msg.HeaderBody, headerAuthentication: Msg.HeaderAuthentication, frames: seq<MessageBody.Frame>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires headerBody.Valid()
    decreases signature, headerBody, headerAuthentication, frames
  {
    ghost var serializedMessage: seq<uint8> := SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames);
    |signature| < UINT16_LIMIT &&
    exists material: Crypto.EncryptionMaterials | material.signingKey.Some? :: 
      Signature.IsSigned(material.signingKey.value, serializedMessage, signature)
  }

  method Encrypt(request: EncryptRequest) returns (res: Result<seq<uint8>, string>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures request.algorithmSuiteID.Some? && request.algorithmSuiteID.value !in AlgorithmSuite.VALID_IDS ==> res.Failure?
    ensures request.frameLength.Some? && request.frameLength.value == 0 ==> res.Failure?
    ensures match res { case Success(_mcc#0) => (var encryptedSequence := _mcc#0; exists headerBody, headerAuthentication, frames :: ValidHeaderBodyForRequest(headerBody, request) && ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody) && ValidFramesForRequest(frames, request, headerBody) && match headerBody.algorithmSuiteID.SignatureType() { case Some(_v1) => (exists signature | ValidSignatureForRequest(signature, headerBody, headerAuthentication, frames) :: encryptedSequence == SerializeMessageWithSignature(headerBody, headerAuthentication, frames, signature)) case None => encryptedSequence == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames) }) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases request
  {
    if request.cmm != null && request.keyring != null {
      return Failure(""EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both)."");
    } else if request.cmm == null && request.keyring == null {
      return Failure(""EncryptRequest.cmm and EncryptRequest.keyring cannot both be null."");
    } else if request.algorithmSuiteID.Some? && request.algorithmSuiteID.value !in AlgorithmSuite.VALID_IDS {
      return Failure(""Invalid algorithmSuiteID."");
    } else if request.frameLength.Some? && request.frameLength.value == 0 {
      return Failure(""Request frameLength must be > 0"");
    }
    var cmm: Crypto.ICryptographicMaterialsManager;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }
    var frameLength := if request.frameLength.Some? then request.frameLength.value else DEFAULT_FRAME_LENGTH;
    var algorithmSuiteID := if request.algorithmSuiteID.Some? then Some(AlgorithmSuite.InternalIDToPolymorphID(request.algorithmSuiteID.value as AlgorithmSuite.ID)) else None;
    expect request.plaintextLength < INT64_MAX_LIMIT, ""expectation violation""
    var encMatRequest := Crypto.GetEncryptionMaterialsInput(encryptionContext := request.encryptionContext, algorithmSuiteId := algorithmSuiteID, maxPlaintextLength := Option.Some(request.plaintextLength as int64));
    var output :- cmm.GetEncryptionMaterials(encMatRequest);
    var encMat := output.encryptionMaterials;
    expect encMat.plaintextDataKey.Some?, ""expectation violation""
    expect algorithmSuiteID.None? || (request.algorithmSuiteID.value as AlgorithmSuite.ID).SignatureType().Some? ==> Materials.EC_PUBLIC_KEY_FIELD in encMat.encryptionContext, ""expectation violation""
    expect DefaultCMMDef.Serializable(encMat), ""expectation violation""
    expect match request.algorithmSuiteID { case None => AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId) == 888 as AlgorithmSuite.ID case Some(_mcc#3) => var id := _mcc#3; AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId) == id as AlgorithmSuite.ID }, ""expectation violation""
    expect |encMat.plaintextDataKey.value| == AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).KDFInputKeyLength(), ""expectation violation""
    if UINT16_LIMIT <= |encMat.encryptedDataKeys| {
      return Failure(""Number of EDKs exceeds the allowed maximum."");
    }
    var messageID: Msg.MessageID :- Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(encMat.plaintextDataKey.value, AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId), messageID);
    var headerBody := Msg.HeaderBody(Msg.VERSION_1, Msg.TYPE_CUSTOMER_AED, AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId), messageID, encMat.encryptionContext, Msg.EncryptedDataKeys(encMat.encryptedDataKeys), Msg.ContentType.Framed, AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).IVLength() as uint8, frameLength);
    assert ValidHeaderBodyForRequest(headerBody, request);
    ghost var serializedHeaderBody := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(headerBody));
    var wr := new Streams.ByteWriter();
    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.GetDataWritten();
    assert unauthenticatedHeader == serializedHeaderBody;
    var iv: seq<uint8> := seq(AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).IVLength(), (_: int) => 0);
    var encryptionOutput :- AESEncryption.AESEncryptExtern(AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    assert ValidHeaderAuthenticationForRequest(headerAuthentication, headerBody) by {
      assert headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), (_: int) => 0);
      assert Msg.HeaderAuthenticationMatchesHeaderBody(headerAuthentication, headerBody);
      assert IsDerivedKey(derivedDataKey) && AESEncryption.EncryptedWithKey(encryptionOutput.cipherText, derivedDataKey);
    }
    ghost var serializedHeaderAuthentication := headerAuthentication.iv + headerAuthentication.authenticationTag;
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId));
    assert wr.GetDataWritten() == serializedHeaderBody + serializedHeaderAuthentication;
    var seqWithGhostFrames :- MessageBody.EncryptMessageBody(request.plaintext, frameLength as int, messageID, derivedDataKey, AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId));
    var body := seqWithGhostFrames.sequence;
    ghost var frames := seqWithGhostFrames.frames;
    assert ValidFramesForRequest(frames, request, headerBody) && body == MessageBody.FramesToSequence(frames) by {
      assert forall frame: MessageBody.Frame | frame in frames :: frame.Valid();
      assert MessageBody.FramesEncryptPlaintext(frames, request.plaintext);
      assert forall frame: MessageBody.Frame | frame in frames :: |frame.iv| == headerBody.algorithmSuiteID.IVLength();
      assert IsDerivedKey(derivedDataKey);
      assert forall frame: MessageBody.Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, derivedDataKey);
    }
    var msg := wr.GetDataWritten() + body;
    if AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).SignatureType().Some? {
      var ecdsaParams := AlgorithmSuite.PolymorphIDToInternalID(encMat.algorithmSuiteId).SignatureType().value;
      expect encMat.signingKey.Some?, ""expectation violation""
      var bytes :- Signature.Sign(ecdsaParams, encMat.signingKey.value, msg);
      if |bytes| != ecdsaParams.SignatureLength() as int {
        return Failure(""Malformed response from Sign()."");
      }
      var signature := UInt16ToSeq(|bytes| as uint16) + bytes;
      assert ValidSignatureForRequest(bytes, headerBody, headerAuthentication, frames) by {
        assert |signature| < UINT16_LIMIT;
        assert Signature.IsSigned(encMat.signingKey.value, msg, bytes);
      }
      msg := msg + signature;
      assert headerBody.algorithmSuiteID.SignatureType().Some?;
      assert msg == SerializeMessageWithSignature(headerBody, headerAuthentication, frames, bytes);
      return Success(msg);
    } else {
      assert msg == SerializeMessageWithoutSignature(headerBody, headerAuthentication, frames);
      return Success(msg);
    }
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID)
      returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
    ensures IsDerivedKey(derivedDataKey)
    decreases plaintextDataKey, algorithmSuiteID, messageID
  {
    var algorithm := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if algorithm == KeyDerivationAlgorithms.IDENTITY {
      assert IsDerivedKey(plaintextDataKey) by {
        reveal IsDerivedKey();
      }
      return plaintextDataKey;
    }
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.Hkdf(algorithm, None, plaintextDataKey, infoSeq, len);
    assert IsDerivedKey(derivedKey) by {
      reveal IsDerivedKey();
    }
    return derivedKey;
  }

  predicate {:opaque} {:fuel 0, 0} IsDerivedKey(derivedDataKey: seq<uint8>)
    decreases derivedDataKey
  {
    true
  }

  method Decrypt(request: DecryptRequest) returns (res: Result<seq<uint8>, string>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    decreases request
  {
    var decryptWithVerificationInfo :- DecryptWithVerificationInfo(request);
    return Success(decryptWithVerificationInfo.plaintext);
  }

  method DecryptWithVerificationInfo(request: DecryptRequest) returns (res: Result<DecryptResultWithVerificationInfo, string>)
    ensures request.cmm == null && request.keyring == null ==> res.Failure?
    ensures request.cmm != null && request.keyring != null ==> res.Failure?
    ensures match res { case Success(_mcc#0) => (var d := _mcc#0; d.header.body.Valid() && Msg.IsSerializationOfHeaderBody(d.hbSeq, d.header.body) && (d.header.body.contentType.Framed? ==> (forall frame: MessageBody.Frame | frame in d.frames :: frame.Valid()) && MessageBody.FramesEncryptPlaintext(d.frames, d.plaintext) && match d.signature { case Some(_v6) => |d.signature.value| < UINT16_LIMIT && request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag + MessageBody.FramesToSequence(d.frames) + UInt16ToSeq(|d.signature.value| as uint16) + d.signature.value case None => request.message == d.hbSeq + d.header.auth.iv + d.header.auth.authenticationTag + MessageBody.FramesToSequence(d.frames) })) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases request
  {
    if request.cmm != null && request.keyring != null {
      return Failure(""DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both)."");
    } else if request.cmm == null && request.keyring == null {
      return Failure(""DecryptRequest.cmm and DecryptRequest.keyring cannot both be null."");
    }
    var cmm: Crypto.ICryptographicMaterialsManager;
    if request.keyring == null {
      cmm := request.cmm;
    } else {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(request.keyring);
    }
    var rd := new Streams.ByteReader(request.message);
    var deserializeHeaderResult :- Deserialize.DeserializeHeader(rd);
    var header := deserializeHeaderResult.header;
    if header.body.contentType.Framed? {
      assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..rd.reader.pos]) by {
        reveal HeaderBySequence();
        assert header.body.contentType.Framed?;
        assert header.body.Valid();
        assert Msg.IsSerializationOfHeaderBody(deserializeHeaderResult.hbSeq, header.body);
        assert rd.reader.data[..rd.reader.pos] == deserializeHeaderResult.hbSeq + header.auth.iv + header.auth.authenticationTag;
      }
      assert DataIsFramed(request.message) by {
        assert 0 <= rd.reader.pos <= |request.message|;
        assert rd.reader.data[..rd.reader.pos] == request.message[..rd.reader.pos];
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..rd.reader.pos]);
      }
    }
    var decMatRequest := Crypto.DecryptMaterialsInput(algorithmSuiteId := AlgorithmSuite.InternalIDToPolymorphID(header.body.algorithmSuiteID), encryptedDataKeys := header.body.encryptedDataKeys.entries, encryptionContext := header.body.aad);
    var output :- cmm.DecryptMaterials(decMatRequest);
    var decMat := output.decryptionMaterials;
    expect decMat.plaintextDataKey.Some?, ""expectation violation""
    expect |decMat.plaintextDataKey.value| == AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId).KDFInputKeyLength(), ""expectation violation""
    var decryptionKey := DeriveKey(decMat.plaintextDataKey.value, AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId), header.body.messageID);
    ghost var endHeaderPos := rd.reader.pos;
    var plaintext;
    match header.body.contentType {
      case {:split false} NonFramed() =>
        plaintext :- MessageBody.DecryptNonFramedMessageBody(rd, AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId), decryptionKey, header.body.messageID);
      case {:split false} Framed() =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId), decryptionKey, header.body.frameLength as int, header.body.messageID);
    }
    assert header.body.contentType.Framed? ==> exists frames: seq<MessageBody.Frame> | |frames| < UINT32_LIMIT && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid()) && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos .. rd.reader.pos] :: true && MessageBody.FramesEncryptPlaintext(frames, plaintext);
    ghost var frames: seq<MessageBody.Frame> :| header.body.contentType.Framed? ==> |frames| < UINT32_LIMIT && (forall frame: MessageBody.Frame | frame in frames :: frame.Valid()) && MessageBody.FramesToSequence(frames) == rd.reader.data[endHeaderPos .. rd.reader.pos] && MessageBody.FramesEncryptPlaintext(frames, plaintext);
    if header.body.contentType.Framed? {
      assert FramesBySequence(frames, rd.reader.data[endHeaderPos .. rd.reader.pos]) by {
        reveal FramesBySequence();
        assert |frames| < UINT32_LIMIT;
        assert forall frame: MessageBody.Frame | frame in frames :: frame.Valid();
        assert rd.reader.data[endHeaderPos .. rd.reader.pos] == MessageBody.FramesToSequence(frames);
      }
      assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]) by {
        assert endHeaderPos == |deserializeHeaderResult.hbSeq| + |header.auth.iv + header.auth.authenticationTag|;
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]);
      }
      assert FramesBySequence(frames, rd.reader.data[endHeaderPos .. rd.reader.pos]);
    }
    ghost var signature: Option<seq<uint8>> := None;
    ghost var endFramePos := rd.reader.pos;
    assert header.body.contentType.Framed? ==> 0 <= endHeaderPos <= endFramePos <= |request.message|;
    if AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId).SignatureType().Some? {
      var verifyResult, locSig := VerifySignature(rd, decMat);
      signature := Some(locSig);
      if verifyResult.Failure? {
        return Failure(verifyResult.error);
      }
      assert SignatureBySequence(signature.value, rd.reader.data[endFramePos .. rd.reader.pos]);
    }
    var isDone := rd.IsDoneReading();
    if !isDone {
      return Failure(""message contains additional bytes at end"");
    }
    if header.body.contentType.Framed? {
      if AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId).SignatureType().Some? {
        assert signature.Some?;
        assert SignatureBySequence(signature.value, rd.reader.data[endFramePos .. rd.reader.pos]);
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos]) && FramesBySequence(frames, request.message[endHeaderPos .. endFramePos]) && SignatureBySequence(signature.value, request.message[endFramePos..]) by {
          assert 0 <= endHeaderPos <= endFramePos <= |request.message|;
          assert SignatureBySequence(signature.value, request.message[endFramePos..]) by {
            assert header.body.contentType.Framed? ==> SignatureBySequence(signature.value, rd.reader.data[endFramePos .. rd.reader.pos]);
            assert rd.reader.data[endFramePos .. rd.reader.pos] == request.message[endFramePos..] by {
              calc {
                rd.reader.data[endFramePos .. rd.reader.pos];
              ==
                {
                  UpperBoundRemv(rd.reader.data, endFramePos);
                  assert rd.reader.pos == |rd.reader.data|;
                }
                rd.reader.data[endFramePos..];
              ==
                {
                  assert rd.reader.data == request.message;
                }
                request.message[endFramePos..];
              }
            }
            assert SignatureBySequence(signature.value, rd.reader.data[endFramePos .. rd.reader.pos]);
          }
        }
        HBandMBwithSigMatchSequence(header, deserializeHeaderResult.hbSeq, frames, signature.value, request.message);
      } else {
        assert signature.None?;
        assert 0 <= endHeaderPos <= |request.message| by {
          assert request.message == rd.reader.data;
        }
        assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, request.message[..endHeaderPos]) && FramesBySequence(frames, request.message[endHeaderPos..]) by {
          assert HeaderBySequence(header, deserializeHeaderResult.hbSeq, rd.reader.data[..endHeaderPos]) && FramesBySequence(frames, rd.reader.data[endHeaderPos .. rd.reader.pos]);
          assert rd.reader.data[endHeaderPos .. rd.reader.pos] == request.message[endHeaderPos..] by {
            calc {
              rd.reader.data[endHeaderPos .. rd.reader.pos];
            ==
              {
                UpperBoundRemv(rd.reader.data, endHeaderPos);
              }
              rd.reader.data[endHeaderPos..];
            ==
              {
                assert rd.reader.data == request.message;
              }
              request.message[endHeaderPos..];
            }
          }
        }
        assert 0 <= endHeaderPos <= |request.message|;
        HBandMBMatchSequence(header, deserializeHeaderResult.hbSeq, frames, request.message);
      }
    }
    var decryptResultWithVerificationInfo := DecryptResultWithVerificationInfo(plaintext, header, deserializeHeaderResult.hbSeq, frames, signature);
    return Success(decryptResultWithVerificationInfo);
  }

  method VerifySignature(rd: Streams.ByteReader, decMat: Crypto.DecryptionMaterials)
      returns (res: Result<(), string>, ghost signature: seq<uint8>)
    requires rd.Valid()
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res { case Success(_mcc#0) => 2 <= old(rd.reader.pos) + 2 <= rd.reader.pos && SignatureBySequence(signature, rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) case Failure(_mcc#1) => true }
    decreases rd, decMat
  {
    expect AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId).SignatureType().Some?, ""expectation violation""
    var ecdsaParams := AlgorithmSuite.PolymorphIDToInternalID(decMat.algorithmSuiteId).SignatureType().value;
    var usedCapacity := rd.GetSizeRead();
    assert usedCapacity == rd.reader.pos;
    var msg := rd.reader.data[..usedCapacity];
    var signatureLengthResult := rd.ReadUInt16();
    if signatureLengthResult.Failure? {
      return Failure(signatureLengthResult.error), [];
    }
    var sigResult := rd.ReadBytes(signatureLengthResult.value as nat);
    if sigResult.Failure? {
      return Failure(sigResult.error), [];
    }
    expect decMat.verificationKey.Some?, ""expectation violation""
    var signatureVerifiedResult := Signature.Verify(ecdsaParams, decMat.verificationKey.value, msg, sigResult.value);
    if signatureVerifiedResult.Failure? {
      return Failure(signatureVerifiedResult.error), [];
    }
    if !signatureVerifiedResult.value {
      return Failure(""signature not verified""), [];
    }
    assert SignatureBySequence(sigResult.value, rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]) by {
      reveal SignatureBySequence();
    }
    return Success(()), sigResult.value;
  }

  predicate {:opaque} {:fuel 0, 0} HeaderBySequence(header: Msg.Header, hbSeq: seq<uint8>, sequence: seq<uint8>)
    decreases header, hbSeq, sequence
  {
    header.body.contentType.Framed? &&
    header.body.Valid() &&
    Msg.IsSerializationOfHeaderBody(hbSeq, header.body) &&
    sequence == hbSeq + header.auth.iv + header.auth.authenticationTag
  }

  predicate {:opaque} {:fuel 0, 0} FramesBySequence(frames: seq<MessageBody.Frame>, sequence: seq<uint8>)
    decreases frames, sequence
  {
    |frames| < UINT32_LIMIT &&
    (forall frame: MessageBody.Frame | frame in frames :: 
      frame.Valid()) &&
    sequence == MessageBody.FramesToSequence(frames)
  }

  predicate {:opaque} {:fuel 0, 0} SignatureBySequence(signature: seq<uint8>, sequence: seq<uint8>)
    decreases signature, sequence
  {
    |signature| < UINT16_LIMIT &&
    sequence == UInt16ToSeq(|signature| as uint16) + signature
  }

  lemma /*{:_induction frames}*/ HBandMBMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag|
    requires exists headerLength: int | 0 <= headerLength <= |message| :: HeaderBySequence(header, hbSeq, message[..headerLength]) && FramesBySequence(frames, message[headerLength..])
    ensures message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames)
    decreases header, hbSeq, frames, message
  {
    reveal HeaderBySequence(), FramesBySequence();
  }

  lemma /*{:_induction frames}*/ HBandMBwithSigMatchSequence(header: Msg.Header, hbSeq: seq<uint8>, frames: seq<MessageBody.Frame>, signature: seq<uint8>, message: seq<uint8>)
    requires forall frame: MessageBody.Frame | frame in frames :: frame.Valid()
    requires |message| >= |hbSeq| + |header.auth.iv + header.auth.authenticationTag| + |MessageBody.FramesToSequence(frames)|
    requires exists headerLength: int, frameLength: int | 0 <= headerLength <= frameLength < |message| :: HeaderBySequence(header, hbSeq, message[..headerLength]) && FramesBySequence(frames, message[headerLength .. frameLength]) && SignatureBySequence(signature, message[frameLength..])
    ensures |signature| < UINT16_LIMIT && message == hbSeq + header.auth.iv + header.auth.authenticationTag + MessageBody.FramesToSequence(frames) + UInt16ToSeq(|signature| as uint16) + signature
    decreases header, hbSeq, frames, signature, message
  {
    reveal HeaderBySequence(), FramesBySequence(), SignatureBySequence();
  }

  lemma UpperBoundRemv(sequence: seq<uint8>, lo: int)
    requires 0 <= lo <= |sequence|
    ensures sequence[lo .. |sequence|] == sequence[lo..]
    decreases sequence, lo
  {
  }

  predicate DataIsFramed(sequence: seq<uint8>)
    decreases sequence
  {
    exists i: int, header: Msg.Header, hbSeq: seq<uint8> | 0 <= i <= |sequence| :: 
      HeaderBySequence(header, hbSeq, sequence[..i])
  }
}

module {:extern ""EncryptionContext""} EncryptionContext {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import Sets = Sets
  type Map = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

  type Linear = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  predicate method {:opaque} {:fuel 0, 0} Serializable(encryptionContext: Map)
    decreases encryptionContext
  {
    SerializableKVPairs(encryptionContext) &&
    Length(encryptionContext) < UINT16_LIMIT
  }

  predicate method SerializableKVPairs(encryptionContext: Map)
    decreases encryptionContext
  {
    |encryptionContext| < UINT16_LIMIT &&
    forall key: UTF8.ValidUTF8Bytes :: 
      key in encryptionContext.Keys ==>
        SerializableKVPair((key, encryptionContext[key]))
  }

  predicate method SerializableKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes))
    decreases kvPair
  {
    |kvPair.0| < UINT16_LIMIT &&
    |kvPair.1| < UINT16_LIMIT &&
    UTF8.ValidUTF8Seq(kvPair.0) &&
    UTF8.ValidUTF8Seq(kvPair.1)
  }

  predicate SerializableUnsortedLinear(linear: Linear)
    decreases linear
  {
    |linear| < UINT16_LIMIT &&
    (forall i: int :: 
      0 <= i < |linear| ==>
        SerializableKVPair(linear[i])) &&
    LinearIsUnique(linear)
  }

  predicate SerializableLinear(linear: Linear)
    decreases linear
  {
    LinearSorted(linear) &&
    SerializableUnsortedLinear(linear)
  }

  predicate LinearIsUnique(linear: Linear)
    decreases linear
  {
    forall i: int, j: int | 0 <= i < j < |linear| :: 
      linear[i].0 != linear[j].0
  }

  function method Length(encryptionContext: Map): nat
    decreases encryptionContext
  {
    if |encryptionContext| == 0 then
      0
    else
      var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less); var kvPairs: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)> := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]])); 2 + LinearLength(kvPairs, 0, |kvPairs|)
  }

  function method LinearLength(kvPairs: Linear, lo: nat, hi: nat): nat
    requires lo <= hi <= |kvPairs|
    decreases kvPairs, lo, hi
  {
    if lo == hi then
      0
    else
      LinearLength(kvPairs, lo, hi - 1) + 2 + |kvPairs[hi - 1].0| + 2 + |kvPairs[hi - 1].1|
  }

  method {:extern ""LinearToMap""} LinearToMap(kvPairs: Linear) returns (res: Map)
    ensures (reveal Serializable(); Serializable(res) && SerializableLinear(kvPairs) ==> MapToSeq(res) == if |res| == 0 then [] else UInt16ToSeq(|kvPairs| as uint16) + LinearToSeq(kvPairs, 0, |kvPairs|))
    decreases kvPairs

  lemma /*{:_induction kvPairs, lo, mid, hi}*/ LinearSplit(kvPairs: Linear, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |kvPairs|
    ensures LinearLength(kvPairs, lo, hi) == LinearLength(kvPairs, lo, mid) + LinearLength(kvPairs, mid, hi)
    decreases kvPairs, lo, mid, hi
  {
  }

  lemma /*{:_induction kvPairs, more}*/ LinearPrefix(kvPairs: Linear, more: Linear)
    ensures LinearLength(kvPairs + more, 0, |kvPairs|) == LinearLength(kvPairs, 0, |kvPairs|)
    decreases kvPairs, more
  {
    ghost var n := |kvPairs|;
    if n == 0 {
    } else {
      ghost var last := kvPairs[n - 1];
      calc {
        LinearLength(kvPairs + more, 0, n);
      ==
        LinearLength(kvPairs + more, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==
        {
          assert kvPairs + more == kvPairs[..n - 1] + ([last] + more);
        }
        LinearLength(kvPairs[..n - 1] + ([last] + more), 0, n - 1) + 4 + |last.0| + |last.1|;
      ==
        {
          LinearPrefix(kvPairs[..n - 1], [last] + more);
        }
        LinearLength(kvPairs[..n - 1], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==
        {
          LinearPrefix(kvPairs[..n - 1], [last] + more);
        }
        LinearLength(kvPairs[..n - 1] + [last], 0, n - 1) + 4 + |last.0| + |last.1|;
      ==
        {
          assert kvPairs[..n - 1] + [last] == kvPairs;
        }
        LinearLength(kvPairs, 0, n - 1) + 4 + |last.0| + |last.1|;
      ==
        LinearLength(kvPairs, 0, n);
      }
    }
  }

  lemma /*{:_induction kvPairs}*/ LinearExtend(kvPairs: Linear, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    ensures LinearLength(kvPairs + [(key, value)], 0, |kvPairs| + 1) == LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases kvPairs, key, value
  {
    LinearPrefix(kvPairs, [(key, value)]);
  }

  lemma /*{:_induction kvPairs}*/ LinearInsert(kvPairs: Linear, insertionPoint: nat, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    requires insertionPoint <= |kvPairs|
    ensures ghost var kvPairs': seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)> := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]; LinearLength(kvPairs', 0, |kvPairs'|) == LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases |kvPairs|
  {
    ghost var kvPairs' := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..];
    if |kvPairs| == insertionPoint {
      assert kvPairs' == kvPairs + [(key, value)];
      LinearExtend(kvPairs, key, value);
    } else {
      ghost var m := |kvPairs| - 1;
      var (d0, d1) := kvPairs[m];

      ghost var a, b, c, d := kvPairs[..insertionPoint], [(key, value)], kvPairs[insertionPoint .. m], [(d0, d1)];
      assert kvPairs == a + c + d;
      assert kvPairs' == a + b + c + d;
      ghost var ac := a + c;
      ghost var abc := a + b + c;
      calc {
        LinearLength(kvPairs', 0, |kvPairs'|);
        LinearLength(abc + [(d0, d1)], 0, |abc| + 1);
      ==
        {
          LinearExtend(abc, d0, d1);
        }
        LinearLength(abc, 0, |abc|) + 4 + |d0| + |d1|;
      ==
        {
          LinearInsert(ac, insertionPoint, key, value);
        }
        LinearLength(ac, 0, |ac|) + 4 + |key| + |value| + 4 + |d0| + |d1|;
      ==
        {
          LinearExtend(ac, d0, d1);
        }
        LinearLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|;
      }
    }
  }

  method ComputeLength(encryptionContext: Map) returns (res: nat)
    ensures res as nat == Length(encryptionContext)
    decreases encryptionContext
  {
    reveal Serializable();
    if |encryptionContext| == 0 {
      return 0;
    }
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    var len := 2;
    var i := 0;
    while i < |kvPairs|
      invariant i <= |kvPairs|
      invariant 2 + LinearLength(kvPairs, 0, i as int) == len as int
      decreases |kvPairs| - i
    {
      var kvPair := kvPairs[i];
      len := len + 4 + |kvPair.0| + |kvPair.1|;
      LinearSplit(kvPairs, 0, i + 1, |kvPairs| as int);
      i := i + 1;
    }
    assert len == 2 + LinearLength(kvPairs, 0, |kvPairs|);
    assert len == Length(encryptionContext);
    return len;
  }

  method CheckSerializable(encryptionContext: Map) returns (res: bool)
    ensures res == Serializable(encryptionContext)
    decreases encryptionContext
  {
    reveal Serializable();
    if |encryptionContext| == 0 {
      return true;
    } else if |encryptionContext| >= UINT16_LIMIT {
      return false;
    }
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence<uint8>(encryptionContext.Keys, UInt.UInt8Less);
    var kvPairs := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    assert forall i: int :: 0 <= i < |keys| ==> kvPairs[i] == (keys[i], encryptionContext[keys[i]]);
    var kvPairsLen := 2;
    var i := 0;
    while i < |kvPairs|
      invariant i <= |kvPairs|
      invariant forall k: int :: 0 <= k < i ==> SerializableKVPair(kvPairs[k])
      invariant 2 + LinearLength(kvPairs, 0, i as int) == kvPairsLen as int < UINT16_LIMIT
      decreases |kvPairs| - i
    {
      var kvPair := kvPairs[i];
      kvPairsLen := kvPairsLen + 4 + |kvPair.0| + |kvPair.1|;
      LinearSplit(kvPairs, 0, i as int + 1, |kvPairs| as int);
      if !(|kvPair.0| < UINT16_LIMIT && |kvPair.1| < UINT16_LIMIT) {
        assert kvPair.0 in encryptionContext.Keys;
        return false;
      } else if kvPairsLen >= UINT16_LIMIT {
        return false;
      }
      assert forall k: int :: 0 <= k < i ==> SerializableKVPair(kvPairs[k]);
      assert kvPairsLen < UINT16_LIMIT;
      i := i + 1;
    }
    return true;
  }

  predicate LinearSortedUpTo(a: Linear, n: nat)
    requires n <= |a|
    decreases a, n
  {
    forall j: int :: 
      0 < j < n ==>
        LexicographicLessOrEqual(a[j - 1].0, a[j].0, UInt.UInt8Less)
  }

  predicate LinearSorted(kvPairs: Linear)
    decreases kvPairs
  {
    LinearSortedUpTo(kvPairs, |kvPairs|)
  }

  predicate StrongLinearSorted(kvPairs: Linear)
    decreases kvPairs
  {
    forall i: int, j: int | 0 <= i < j < |kvPairs| :: 
      LexicographicLessOrEqual(kvPairs[i].0, kvPairs[j].0, UInt.UInt8Less)
  }

  lemma LinearSortedImpliesStrongLinearSorted(ls: Linear)
    requires LinearSorted(ls)
    ensures StrongLinearSorted(ls)
    decreases ls
  {
    if |ls| <= 1 {
    } else {
      forall i: int, j: int | 0 <= i < j < |ls|
        ensures LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less)
      {
        LinearSortedImpliesStrongLinearSorted(ls[1..]);
        if i == 0 && 2 <= |ls| {
          LexIsReflexive(ls[1].0, UInt.UInt8Less);
          LexIsTransitive(ls[i].0, ls[1].0, ls[j].0, UInt.UInt8Less);
          assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
        } else {
          assert LexicographicLessOrEqual(ls[i].0, ls[j].0, UInt.UInt8Less);
        }
      }
    }
  }

  lemma SortedSequenceIsUnqiue(xs: Linear, ys: Linear)
    requires LinearSorted(xs) && LinearIsUnique(xs)
    requires LinearSorted(ys) && LinearIsUnique(ys)
    requires forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in xs <==> p in ys
    ensures xs == ys
    decreases xs, ys
  {
    LinearSortedImpliesStrongLinearSorted(xs);
    LinearSortedImpliesStrongLinearSorted(ys);
    if xs != [] && ys != [] {
      assert xs[0] == ys[0] by {
        if xs[0] != ys[0] {
          assert forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | p in xs[1..] :: LexicographicLessOrEqual(xs[0].0, p.0, UInt.UInt8Less);
          assert xs[0] in ys[1..] by {
            assert xs[0] != ys[0] && !(xs[0] in ys[1..]) ==> xs[0] !in ys;
          }
          assert forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | p in ys[1..] :: LexicographicLessOrEqual(ys[0].0, p.0, UInt.UInt8Less);
          assert ys[0] in xs[1..] by {
            assert ys[0] != xs[0] && !(ys[0] in xs[1..]) ==> ys[0] !in xs;
          }
          assert LexicographicLessOrEqual(ys[0].0, xs[0].0, UInt.UInt8Less);
          assert LexicographicLessOrEqual(xs[0].0, ys[0].0, UInt.UInt8Less);
          assert false;
        }
      }
      assert forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in xs[1..] <==> p in ys[1..] by {
        if exists p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in xs[1..] && !(p in ys[1..]) {
          ghost var p :| p in xs[1..] && !(p in ys[1..]);
          assert p != ys[0];
          assert p in xs && !(p in ys);
          assert false;
        } else {
          if exists p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in ys[1..] && !(p in xs[1..]) {
            ghost var p :| p in ys[1..] && !(p in xs[1..]);
            assert p != xs[0];
            assert p in xs && !(p in ys);
            assert false;
          }
        }
      }
      SortedSequenceIsUnqiue(xs[1..], ys[1..]);
    } else {
      if xs == [] && ys != [] {
        assert ys[0] in xs;
        assert false;
      }
      if ys == [] && xs != [] {
        assert xs[0] in ys;
        assert false;
      }
    }
  }

  predicate LinearSeqToMap(sequence: seq<uint8>, resultMap: Map)
    decreases sequence, resultMap
  {
    if 2 <= |sequence| && |sequence[2..]| < UINT16_LIMIT then
      sequence[..2] == UInt16ToSeq(|sequence[2..]| as uint16) &&
      SeqToMap(sequence[2..], resultMap)
    else
      false
  }

  predicate SeqToMap(sequence: seq<uint8>, resultMap: Map)
    decreases sequence, resultMap
  {
    if 2 <= |sequence| then
      exists unsortedKvPairs: Linear :: 
        SeqToLinearToMap(sequence, resultMap, unsortedKvPairs, InsertionSort(unsortedKvPairs))
    else
      |resultMap| == 0
  }

  predicate SeqToLinearToMap(sequence: seq<uint8>, resultMap: Map, unsortedKvPairs: Linear, sortedKvPairs: Linear)
    decreases sequence, resultMap, unsortedKvPairs, sortedKvPairs
  {
    2 <= |sequence| &&
    SerializableUnsortedLinear(unsortedKvPairs) &&
    SerializableLinear(sortedKvPairs) &&
    SerializableKVPairs(resultMap) &&
    sequence[..2] == UInt16ToSeq(|resultMap| as uint16) &&
    LinearToUnorderedSeq(unsortedKvPairs, 0, |unsortedKvPairs|) == sequence[2..] &&
    sortedKvPairs == InsertionSort(unsortedKvPairs) &&
    MapToSeq(resultMap) == sequence[..2] + LinearToSeq(sortedKvPairs, 0, |sortedKvPairs|)
  }

  lemma MapToLinearIsDualLinearSeqToMap(resultMap: Map)
    requires Serializable(resultMap)
    ensures LinearSeqToMap(MapToLinear(resultMap), resultMap)
    decreases resultMap
  {
    reveal Serializable();
    LengthCorrect(resultMap);
    MapToSeqIsDualSeqToMap(resultMap);
  }

  function LinearToUnorderedSeq(kvPairs: Linear, lo: nat, hi: nat): seq<uint8>
    requires SerializableUnsortedLinear(kvPairs)
    requires lo <= hi <= |kvPairs|
    decreases kvPairs, lo, hi
  {
    if lo == hi then
      []
    else
      LinearToUnorderedSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  lemma /*{:_induction kvHead, kvTail, lo, hi}*/ LinearToUnorderedSeqInductiveStep(kvHead: Linear, kvTail: Linear, lo: nat, hi: nat)
    requires SerializableUnsortedLinear(kvHead + kvTail)
    requires lo <= hi <= |kvHead|
    ensures SerializableUnsortedLinear(kvHead)
    ensures LinearToUnorderedSeq(kvHead + kvTail, lo, hi) == LinearToUnorderedSeq(kvHead, lo, hi)
    decreases kvHead, kvTail, lo, hi
  {
    assert SerializableUnsortedLinear(kvHead) by {
      assert |kvHead| < UINT16_LIMIT;
      assert forall i: int :: 0 <= i < |kvHead| ==> SerializableKVPair(kvHead[i]) by {
        assert forall pair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: pair in kvHead ==> pair in kvHead + kvTail;
        assert (exists pair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: pair in kvHead && !SerializableKVPair(pair)) ==> exists pair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: pair in kvHead + kvTail && !SerializableKVPair(pair);
      }
      assert LinearIsUnique(kvHead) by {
        ghost var kvPairs := kvHead + kvTail;
        assert forall i: int | 0 <= i < |kvHead| :: kvHead[i] == kvPairs[i];
        assert (exists i: int, j: int | 0 <= i < j < |kvHead| :: kvHead[i] == kvHead[j]) ==> exists i: int, j: int | 0 <= i < j < |kvPairs| :: kvPairs[i] == kvPairs[j];
      }
    }
  }

  lemma MapToSeqIsDualSeqToMap(resultMap: Map)
    requires SerializableKVPairs(resultMap)
    ensures SeqToMap(MapToSeq(resultMap), resultMap)
    decreases resultMap
  {
    ghost var sequenceComplete := MapToSeq(resultMap);
    if sequenceComplete != [] {
      ghost var sequence := sequenceComplete[2..];
      ghost var kvPairs :| (forall i: int :: 0 <= i < |kvPairs| ==> SerializableKVPair(kvPairs[i])) && |kvPairs| < UINT16_LIMIT && LinearSorted(kvPairs) && LinearIsUnique(kvPairs) && LinearToSeq(kvPairs, 0, |kvPairs|) == sequence && sequenceComplete[..2] == UInt16ToSeq(|kvPairs| as uint16);
      InsertionSortPreservesProperties(kvPairs);
      SortedSequenceIsUnqiue(kvPairs, InsertionSort(kvPairs));
      SortedLinearIsFixpointAADDuality(kvPairs);
    } else {
    }
  }

  lemma /*{:_induction linear}*/ SortedLinearIsFixpointAADDuality(linear: Linear)
    requires forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | p in linear :: SerializableKVPair(p)
    requires |linear| < UINT16_LIMIT
    requires LinearIsUnique(linear)
    requires LinearSorted(linear)
    ensures forall hi: int | 0 <= hi <= |linear| :: LinearToUnorderedSeq(linear, 0, hi) == LinearToSeq(linear, 0, hi)
    decreases linear
  {
    SortedLinearIsFixpointAADDualityAux(linear, |linear|);
  }

  lemma /*{:_induction linear}*/ SortedLinearIsFixpointAADDualityAux(linear: Linear, lim: nat)
    requires forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | p in linear :: SerializableKVPair(p)
    requires |linear| < UINT16_LIMIT
    requires LinearIsUnique(linear)
    requires LinearSorted(linear)
    requires lim <= |linear|
    ensures forall hi: int | 0 <= hi <= lim :: LinearToUnorderedSeq(linear, 0, hi) == LinearToSeq(linear, 0, hi)
    decreases linear, lim
  {
    if lim == 0 {
      assert LinearToUnorderedSeq(linear, 0, 0) == LinearToSeq(linear, 0, 0);
    } else {
      SortedLinearIsFixpointAADDualityAux(linear, lim - 1);
      assert LinearToUnorderedSeq(linear, 0, lim) == LinearToSeq(linear, 0, lim);
    }
  }

  lemma /*{:_induction ps}*/ InsertionSortPreservesProperties(ps: Linear)
    requires LinearIsUnique(ps)
    requires forall l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | l in ps :: SerializableKVPair(l)
    ensures LinearIsUnique(InsertionSort(ps))
    ensures forall l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | l in InsertionSort(ps) :: SerializableKVPair(l)
    ensures |InsertionSort(ps)| == |ps|
    decreases ps
  {
    if ps == [] {
    } else {
      ghost var ls := InsertionSort(ps[1..]);
      forall j: int | 0 <= j < |ls|
        ensures ps[0].0 != ls[j].0
      {
        assert ps[0].0 == ls[j].0 ==> ls[j] in ps[1..];
        assert ps[0].0 == ls[j].0 ==> false;
      }
      InsertPairPreservesProperties(ps[0], ls);
    }
  }

  lemma /*{:_induction p, ps}*/ InsertPairPreservesProperties(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear)
    requires LinearSorted(ps)
    requires LinearIsUnique(ps)
    requires forall j: int | 0 <= j < |ps| :: p.0 != ps[j].0
    requires forall l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | l in ps :: SerializableKVPair(l)
    requires SerializableKVPair(p)
    ensures LinearIsUnique(InsertPair(p, ps))
    ensures forall l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | l in InsertPair(p, ps) :: SerializableKVPair(l)
    ensures |InsertPair(p, ps)| == |ps| + 1
    decreases p, ps
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less) {
    } else {
      assert LinearIsUnique([ps[0]] + InsertPair(p, ps[1..])) by {
        ghost var ls := InsertPair(p, ps[1..]);
        ghost var l := ps[0];
        assert !LinearIsUnique([l] + ls) ==> exists m: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) | m in ls :: m.0 == l.0;
      }
    }
  }

  function MapToSeq(kvPairs: Map): seq<uint8>
    requires SerializableKVPairs(kvPairs)
    decreases kvPairs
  {
    ghost var n: int := |kvPairs|;
    if n == 0 then
      []
    else
      ghost var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence<uint8>(kvPairs.Keys, UInt.UInt8Less); ghost var kvPairsSeq: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)> := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], kvPairs[keys[i]])); UInt16ToSeq(n as uint16) + LinearToSeq(kvPairsSeq, 0, |kvPairsSeq|)
  }

  function LinearToSeq(kvPairs: Linear, lo: nat, hi: nat): seq<uint8>
    requires SerializableLinear(kvPairs)
    requires lo <= hi <= |kvPairs|
    decreases kvPairs, lo, hi
  {
    if lo == hi then
      []
    else
      LinearToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function MapToLinear(kvPairs: Map): seq<uint8>
    requires Serializable(kvPairs)
    decreases kvPairs
  {
    reveal Serializable();
    UInt16ToSeq(Length(kvPairs) as uint16) + MapToSeq(kvPairs)
  }

  function KVPairToSeq(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)): seq<uint8>
    requires SerializableKVPair(kvPair)
    decreases kvPair
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  function InsertionSort(linear: Linear): Linear
    ensures ghost var linearSorted: Linear := InsertionSort(linear); (forall p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: p in linear <==> p in linearSorted) && LinearSorted(linearSorted)
    decreases linear
  {
    if linear == [] then
      []
    else
      InsertPair(linear[0], InsertionSort(linear[1..]))
  }

  function InsertPair(p: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), ps: Linear): Linear
    requires LinearSorted(ps)
    ensures ghost var ls: Linear := InsertPair(p, ps); LinearSorted(ls) && forall l: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes) :: l in ps || l == p <==> l in ls
    decreases p, ps
  {
    if ps == [] || LexicographicLessOrEqual(p.0, ps[0].0, UInt.UInt8Less) then
      [p] + ps
    else
      LexIsTotal(p.0, ps[0].0, UInt.UInt8Less); [ps[0]] + InsertPair(p, ps[1..])
  }

  function GetUTF8(sequence: seq<uint8>, length: nat): (res: Option<UTF8.ValidUTF8Bytes>)
    ensures |sequence| >= length && UTF8.ValidUTF8Seq(sequence[..length]) <==> res.Some?
    ensures res.Some? ==> sequence[..length] == res.value
    decreases sequence, length
  {
    if |sequence| >= length then
      ghost var utfSeq: seq<uint8> := sequence[..length];
      if UTF8.ValidUTF8Seq(utfSeq) then
        ghost var utf: UTF8.ValidUTF8Bytes := utfSeq;
        Some(utf)
      else
        None
    else
      None
  }

  lemma DualOfUTF8(utf: UTF8.ValidUTF8Bytes, remainder: seq<uint8>)
    requires |utf| < UINT16_LIMIT && UTF8.ValidUTF8Seq(utf)
    ensures ghost var serializedUtf: seq<uint8> := UInt16ToSeq(|utf| as uint16) + utf + remainder; GetUTF8(serializedUtf[2..], |utf|) == Some(utf)
    decreases utf, remainder
  {
    ghost var serializedUtf := UInt16ToSeq(|utf| as uint16) + utf + remainder;
    assert serializedUtf[2..][..|utf|] == utf;
    ghost var serial := serializedUtf[2..];
    ghost var deserializedUTF := GetUTF8(serial, |utf|);
    assert deserializedUTF.Some? by {
      assert serial[..|utf|] == utf;
      assert |serial| >= |utf| && UTF8.ValidUTF8Seq(serial[..|utf|]);
    }
    assert deserializedUTF.value == serial[..|utf|];
  }

  lemma LengthCorrect(encryptionContext: Map)
    requires Serializable(encryptionContext)
    ensures |MapToLinear(encryptionContext)| == 2 + Length(encryptionContext)
    decreases encryptionContext
  {
    reveal Serializable();
    ghost var keys: seq<UTF8.ValidUTF8Bytes> := SetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    ghost var kvPairs := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    LinearLengthCorrect(kvPairs, 0, |kvPairs|);
  }

  lemma /*{:_induction encryptionContext, lo, hi}*/ LinearLengthCorrect(encryptionContext: Linear, lo: nat, hi: nat)
    requires forall i: int :: 0 <= i < |encryptionContext| ==> SerializableKVPair(encryptionContext[i])
    requires lo <= hi <= |encryptionContext|
    requires |encryptionContext| < UINT16_LIMIT
    requires LinearSorted(encryptionContext)
    requires LinearIsUnique(encryptionContext)
    ensures |LinearToSeq(encryptionContext, lo, hi)| == LinearLength(encryptionContext, lo, hi)
    decreases encryptionContext, lo, hi
  {
  }
}

module AwsKmsMrkAreUnique {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened Seq = Seq

  import opened AwsKmsArnParsing = AwsKmsArnParsing
  function method AwsKmsMrkAreUnique(identifiers: seq<AwsKmsIdentifier>): (result: Result<(), string>)
    decreases identifiers
  {
    var mrks: seq<AwsKmsIdentifier> := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
    if |mrks| == 0 then
      Success(())
    else
      var mrkKeyIds: seq<string> := Seq.Map(GetKeyId, mrks); var setMrks: set<seq<char>> := ToSet(mrkKeyIds); if |mrkKeyIds| == |setMrks| then Success(()) else var duplicateMrkIds: set<seq<char>> := set x: seq<char> {:trigger multiset(mrkKeyIds)[x]} {:trigger x in mrkKeyIds} | x in mrkKeyIds && multiset(mrkKeyIds)[x] >= 1; var isDuplicate: AwsKmsIdentifier -> bool := (identifier: AwsKmsIdentifier) => GetKeyId(identifier) in duplicateMrkIds; var identifierToString: AwsKmsIdentifier -> string := (i: AwsKmsIdentifier) => i.ToString(); var duplicateIdentifiers: seq<AwsKmsIdentifier> := Seq.Filter(isDuplicate, identifiers); var duplicates: seq<string> := Seq.Map(identifierToString, duplicateIdentifiers); Need(|duplicates| > 0, ""Impossible""); Failure(""Related multi-Region keys: "" + Join(duplicates, "","") + ""are not allowed."")
  }

  function method GetKeyId(identifier: AwsKmsIdentifier): (result: string)
    decreases identifier
  {
    match identifier {
      case AwsKmsArnIdentifier(a) =>
        a.resource.value
      case AwsKmsRawResourceIdentifier(i) =>
        i.value
    }
  }

  lemma /*{:_induction identifiers}*/ AwsKmsMrkAreUniqueCorrect(identifiers: seq<AwsKmsIdentifier>)
    ensures |Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers)| == 0 ==> AwsKmsMrkAreUnique(identifiers).Success?
    ensures ghost var mrks: seq<AwsKmsIdentifier> := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers); ghost var ids: seq<string> := Seq.Map(GetKeyId, mrks); |mrks| > 0 && Seq.HasNoDuplicates(ids) ==> AwsKmsMrkAreUnique(identifiers).Success?
    ensures ghost var mrks: seq<AwsKmsIdentifier> := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers); ghost var ids: seq<string> := Seq.Map(GetKeyId, mrks); |mrks| > 0 && !Seq.HasNoDuplicates(ids) ==> AwsKmsMrkAreUnique(identifiers).Failure?
    decreases identifiers
  {
    ghost var mrks := Seq.Filter(IsMultiRegionAwsKmsIdentifier, identifiers);
    ghost var ids := Seq.Map(GetKeyId, mrks);
    if Seq.HasNoDuplicates(ids) {
      LemmaCardinalityOfSetNoDuplicates(ids);
    }
    if |ToSet(ids)| == |ids| {
      LemmaNoDuplicatesCardinalityOfSet(ids);
    }
  }
}

module {:extern ""AwsKmsMrkAwareSymmetricKeyringDef""} AwsKmsMrkAwareSymmetricKeyringDef {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened AwsKmsArnParsing = AwsKmsArnParsing

  import opened AmazonKeyManagementService = AmazonKeyManagementService

  import opened Seq = Seq

  import opened Actions = Actions

  import opened Constants = Constants

  import opened M = AwsKmsMrkMatchForDecrypt

  import opened KeyringDefs = KeyringDefs

  import Materials = Materials

  import opened KMSUtils = KMSUtils

  import UTF8 = UTF8
  class AwsKmsMrkAwareSymmetricKeyring extends Keyring {
    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const awsKmsArn: AwsKmsIdentifier
    const grantTokens: KMSUtils.GrantTokens

    constructor (client: IAmazonKeyManagementService, awsKmsKey: string, grantTokens: GrantTokens)
      requires ParseAwsKmsIdentifier(awsKmsKey).Success?
      requires UTF8.IsASCIIString(awsKmsKey)
      requires 0 < |awsKmsKey| <= MAX_AWS_KMS_IDENTIFIER_LENGTH
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures this.client == client && this.awsKmsKey == awsKmsKey && this.grantTokens == grantTokens
      decreases client, awsKmsKey, grantTokens
    {
      var parsedAwsKmsId := ParseAwsKmsIdentifier(awsKmsKey);
      this.client := client;
      this.awsKmsKey := awsKmsKey;
      this.awsKmsArn := parsedAwsKmsId.value;
      this.grantTokens := grantTokens;
      Repr := {this};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      true &&
      this in Repr
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
      ensures true && materials.plaintextDataKey.None? ==> GenerateDataKeyCalledWith(client, GenerateDataKeyRequest(materials.encryptionContext, grantTokens, awsKmsKey, materials.algorithmSuiteID.KDFInputKeyLength() as int32))
      ensures materials.plaintextDataKey.None? && res.Success? ==> res.value.plaintextDataKey.Some? && |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1 && materials.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.value) && GenerateDataKeyResult(Last(res.value.encryptedDataKeys).ciphertext, res.value.plaintextDataKey.value)
      ensures true && materials.plaintextDataKey.Some? ==> true && EncryptCalledWith(client, EncryptRequest(materials.encryptionContext, grantTokens, awsKmsKey, materials.plaintextDataKey.value))
      ensures materials.plaintextDataKey.Some? && res.Success? ==> |res.value.encryptedDataKeys| == |materials.encryptedDataKeys| + 1 && EncryptResult(Last(res.value.encryptedDataKeys).ciphertext)
      decreases materials
    {
      if materials.plaintextDataKey.None? {
        var generatorRequest := GenerateDataKeyRequest(materials.encryptionContext, grantTokens, awsKmsKey, materials.algorithmSuiteID.KDFInputKeyLength() as int32);
        var maybeGenerateResponse := GenerateDataKey(client, generatorRequest);
        if maybeGenerateResponse.Failure? {
          return Failure(maybeGenerateResponse.error);
        }
        var generateResponse := maybeGenerateResponse.value;
        :- Need(generateResponse.IsWellFormed(), ""Invalid response from KMS GenerateDataKey"");
        :- Need(ParseAwsKmsIdentifier(generateResponse.keyID).Success?, ""Invalid response from KMS GenerateDataKey:: Invalid Key Id"");
        :- Need(materials.algorithmSuiteID.ValidPlaintextDataKey(generateResponse.plaintext), ""Invalid response from AWS KMS GenerateDataKey: Invalid data key"");
        var providerInfo :- UTF8.Encode(generateResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, ""AWS KMS Key ID too long."");
        var edk := Materials.EncryptedDataKey(PROVIDER_ID, providerInfo, generateResponse.ciphertextBlob);
        var plaintextDataKey := generateResponse.plaintext;
        var result := materials.WithKeys(Some(plaintextDataKey), [edk]);
        return Success(result);
      } else {
        var encryptRequest := KMSUtils.EncryptRequest(materials.encryptionContext, grantTokens, awsKmsKey, materials.plaintextDataKey.value);
        var maybeEncryptResponse := KMSUtils.Encrypt(client, encryptRequest);
        if maybeEncryptResponse.Failure? {
          return Failure(maybeEncryptResponse.error);
        }
        var encryptResponse := maybeEncryptResponse.value;
        :- Need(encryptResponse.IsWellFormed(), ""Invalid response from KMS Encrypt"");
        :- Need(ParseAwsKmsIdentifier(encryptResponse.keyID).Success?, ""Invalid response from AWS KMS Encrypt:: Invalid Key Id"");
        var providerInfo :- UTF8.Encode(encryptResponse.keyID);
        :- Need(|providerInfo| < UINT16_LIMIT, ""AWS KMS Key ID too long."");
        var edk := Materials.EncryptedDataKey(PROVIDER_ID, providerInfo, encryptResponse.ciphertextBlob);
        var result := materials.WithKeys(materials.plaintextDataKey, [edk]);
        return Success(result);
      }
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials, encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
      ensures materials.plaintextDataKey.Some? ==> res.Success? && res.value == materials
      ensures materials.plaintextDataKey.None? && res.Success? ==> res.value.plaintextDataKey.Some? && exists edk: Materials.EncryptedDataKey | edk in encryptedDataKeys :: edk.providerID == PROVIDER_ID && DecryptCalledWith(client, DecryptRequest(awsKmsKey, edk.ciphertext, materials.encryptionContext, grantTokens)) && DecryptResult(awsKmsKey, res.value.plaintextDataKey.value) && materials.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.value)
      decreases materials, encryptedDataKeys
    {
      if materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      var filter := new OnDecryptEncryptedDataKeyFilter(awsKmsArn);
      var edksToAttempt :- FilterWithResult(filter, encryptedDataKeys);
      var decryptClosure := new DecryptSingleEncryptedDataKey(materials, client, awsKmsKey, grantTokens);
      var outcome := ReduceToSuccess(decryptClosure, edksToAttempt);
      return match outcome { case Success(_mcc#0) => (var mat := _mcc#0; assert exists edk | edk in edksToAttempt :: edk in encryptedDataKeys && filter.Ensures(edk, Success(true)) && decryptClosure.Ensures(edk, Success(mat)) && DecryptCalledWith(client, DecryptRequest(awsKmsKey, edk.ciphertext, materials.encryptionContext, grantTokens)) && DecryptResult(awsKmsKey, mat.plaintextDataKey.value); Success(mat)) case Failure(_mcc#1) => var errors := _mcc#1; if |errors| == 0 then Failure(""Unable to decrypt data key: No Encrypted Data Keys found to match."") else var concatString := (s, a) => a + ""\n"" + s; var error := Seq.FoldRight(concatString, errors, ""Unable to decrypt data key:\n""); Failure(error) };
    }
  }

  class OnDecryptEncryptedDataKeyFilter extends ActionWithResult<Materials.EncryptedDataKey, bool, string> {
    const awsKmsKey: AwsKmsIdentifier

    constructor (awsKmsKey: AwsKmsIdentifier)
      decreases awsKmsKey
    {
      this.awsKmsKey := awsKmsKey;
    }

    predicate Ensures(edk: Materials.EncryptedDataKey, res: Result<bool, string>)
      decreases edk, res
    {
      true &&
      (res.Success? &&
      res.value ==>
        edk.providerID == PROVIDER_ID)
    }

    method Invoke(edk: Materials.EncryptedDataKey) returns (res: Result<bool, string>)
      ensures Ensures(edk, res)
      decreases edk
    {
      if edk.providerID != PROVIDER_ID {
        return Success(false);
      }
      if !UTF8.ValidUTF8Seq(edk.providerInfo) {
        return Failure(""Invalid AWS KMS encoding, provider info is not UTF8."");
      }
      var keyId :- UTF8.Decode(edk.providerInfo);
      var arn :- ParseAwsKmsArn(keyId);
      return Success(AwsKmsMrkMatchForDecrypt(awsKmsKey, AwsKmsArnIdentifier(arn)));
    }
  }

  class DecryptSingleEncryptedDataKey extends ActionWithResult<Materials.EncryptedDataKey, Materials.CompleteDecryptionMaterials, string> {
    const materials: Materials.PendingDecryptionMaterials
    const client: IAmazonKeyManagementService
    const awsKmsKey: AwsKmsIdentifierString
    const grantTokens: KMSUtils.GrantTokens

    constructor (materials: Materials.PendingDecryptionMaterials, client: IAmazonKeyManagementService, awsKmsKey: AwsKmsIdentifierString, grantTokens: KMSUtils.GrantTokens)
      ensures this.materials == materials && this.client == client && this.awsKmsKey == awsKmsKey && this.grantTokens == grantTokens
      decreases materials, client, awsKmsKey, grantTokens
    {
      this.materials := materials;
      this.client := client;
      this.awsKmsKey := awsKmsKey;
      this.grantTokens := grantTokens;
    }

    predicate Ensures(edk: Materials.EncryptedDataKey, res: Result<Materials.CompleteDecryptionMaterials, string>)
      decreases edk, res
    {
      res.Success? ==>
        res.value.Valid() &&
        OnDecryptPure(materials, res) &&
        DecryptCalledWith(client, DecryptRequest(awsKmsKey, edk.ciphertext, materials.encryptionContext, grantTokens)) &&
        DecryptResult(awsKmsKey, res.value.plaintextDataKey.value)
    }

    method Invoke(edk: Materials.EncryptedDataKey) returns (res: Result<Materials.CompleteDecryptionMaterials, string>)
      ensures Ensures(edk, res)
      decreases edk
    {
      var decryptRequest := KMSUtils.DecryptRequest(awsKmsKey, edk.ciphertext, materials.encryptionContext, grantTokens);
      var decryptResponse :- KMSUtils.Decrypt(client, decryptRequest);
      :- Need(decryptResponse.keyID == awsKmsKey && materials.algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext), ""Invalid response from KMS Decrypt"");
      var result := materials.WithPlaintextDataKey(decryptResponse.plaintext);
      return Success(result);
    }
  }
}

module AwsKmsMrkMatchForDecrypt {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened Seq = Seq

  import opened AwsKmsArnParsing = AwsKmsArnParsing
  predicate method AwsKmsMrkMatchForDecrypt(configuredAwsKmsIdentifier: AwsKmsIdentifier, messageAwsKmsIdentifer: AwsKmsIdentifier)
    decreases configuredAwsKmsIdentifier, messageAwsKmsIdentifer
  {
    if configuredAwsKmsIdentifier == messageAwsKmsIdentifer then
      true
    else
      match (messageAwsKmsIdentifer, configuredAwsKmsIdentifier) { case _#Make2(_mcc#0, _mcc#1) => match _mcc#0 { case AwsKmsArnIdentifier(_mcc#2) => match _mcc#1 { case AwsKmsArnIdentifier(_mcc#4) => (var messageAwsKmsArn := _mcc#4; var configuredAwsKmsArn := _mcc#2; if !IsMultiRegionAwsKmsArn(configuredAwsKmsArn) || !IsMultiRegionAwsKmsArn(messageAwsKmsArn) then false else messageAwsKmsArn.partition == configuredAwsKmsArn.partition && messageAwsKmsArn.service == configuredAwsKmsArn.service && messageAwsKmsArn.account == configuredAwsKmsArn.account && messageAwsKmsArn.resource == configuredAwsKmsArn.resource) case AwsKmsRawResourceIdentifier(_mcc#6) => false } case AwsKmsRawResourceIdentifier(_mcc#8) => false } }
  }

  lemma AwsKmsMrkMatchForDecryptCorrect(config: string, message: string)
    ensures ghost var c: Result<AwsKmsIdentifier, string> := ParseAwsKmsIdentifier(config); ghost var m: Result<AwsKmsIdentifier, string> := ParseAwsKmsIdentifier(message); config == message && c.Success? && m.Success? ==> AwsKmsMrkMatchForDecrypt(c.value, m.value)
    ensures ghost var c: Result<AwsKmsArn, seq<char>> := ParseAwsKmsArn(config); ghost var m: Result<AwsKmsArn, seq<char>> := ParseAwsKmsArn(message); config != message && c.Success? && m.Success? && IsMultiRegionAwsKmsArn(c.value) != IsMultiRegionAwsKmsArn(m.value) ==> !AwsKmsMrkMatchForDecrypt(AwsKmsArnIdentifier(c.value), AwsKmsArnIdentifier(m.value))
    ensures ghost var c: Result<AwsArn, seq<char>> := ParseAwsKmsArn(config); ghost var m: Result<AwsArn, seq<char>> := ParseAwsKmsArn(message); c.Success? && m.Success? && IsMultiRegionAwsKmsArn(c.value) && IsMultiRegionAwsKmsArn(m.value) ==> AwsKmsMrkMatchForDecrypt(AwsKmsArnIdentifier(c.value), AwsKmsArnIdentifier(m.value)) == (m.value.partition == c.value.partition && m.value.service == c.value.service && m.value.account == c.value.account && m.value.resource == c.value.resource)
    decreases config, message
  {
  }
}

module Constants {

  import UTF8 = UTF8
  const PROVIDER_ID: UTF8.ValidUTF8Bytes := var s: seq<uint8> := [97, 119, 115, 45, 107, 109, 115]; assert UTF8.ValidUTF8Range(s, 0, 7); s
}

module {:extern ""KeyringDefs""} KeyringDefs {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import AlgorithmSuite = AlgorithmSuite
  trait {:termination false} Keyring {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnEncryptPure(materials, res)
      decreases materials

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials, encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials, string>)
      requires Valid()
      ensures Valid()
      ensures OnDecryptPure(materials, res)
      decreases materials, encryptedDataKeys
  }

  predicate OnEncryptPure(materials: Materials.ValidEncryptionMaterials, res: Result<Materials.ValidEncryptionMaterials, string>)
    decreases materials, res
  {
    res.Success? ==>
      materials.encryptionContext == res.value.encryptionContext &&
      materials.algorithmSuiteID == res.value.algorithmSuiteID &&
      materials.encryptedDataKeys <= res.value.encryptedDataKeys &&
      materials.signingKey == res.value.signingKey &&
      (materials.plaintextDataKey.Some? ==>
        res.value.plaintextDataKey == materials.plaintextDataKey)
  }

  predicate OnDecryptPure(materials: Materials.ValidDecryptionMaterials, res: Result<Materials.ValidDecryptionMaterials, string>)
    decreases materials, res
  {
    (res.Success? &&
    materials.plaintextDataKey.Some? ==>
      true &&
      materials == res.value) &&
    (res.Success? &&
    materials.plaintextDataKey.None? ==>
      materials.encryptionContext == res.value.encryptionContext &&
      materials.algorithmSuiteID == res.value.algorithmSuiteID &&
      materials.verificationKey == res.value.verificationKey &&
      res.value.plaintextDataKey.Some?)
  }
}

module {:extern ""RawAESKeyringDef""} RawAESKeyringDef {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import Crypto = Aws.Crypto

  import opened UInt = StandardLibrary.UInt

  import EncryptionSuites = EncryptionSuites

  import AlgorithmSuite = AlgorithmSuite

  import Random = Random

  import AESEncryption = AESEncryption

  import Mat = Materials

  import MessageHeader = MessageHeader

  import UTF8 = UTF8

  import EncryptionContext = EncryptionContext

  import Serialize = Serialize

  import Streams = Streams
  class RawAESKeyring extends Crypto.IKeyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: EncryptionSuites.EncryptionSuite

    predicate method Valid()
    {
      |wrappingKey| == wrappingAlgorithm.keyLen as int &&
      wrappingAlgorithm in VALID_ALGORITHMS &&
      wrappingAlgorithm.Valid() &&
      |keyNamespace| < UINT16_LIMIT
    }

    predicate method ValidEncryptionMaterials(mat: Crypto.EncryptionMaterials)
      decreases mat
    {
      (AlgorithmSuite.PolymorphIDToInternalID(mat.algorithmSuiteId).SignatureType().Some? ==>
        mat.signingKey.Some?) &&
      (mat.plaintextDataKey.Some? ==>
        AlgorithmSuite.PolymorphIDToInternalID(mat.algorithmSuiteId).ValidPlaintextDataKey(mat.plaintextDataKey.value)) &&
      (mat.plaintextDataKey.None? ==>
        |mat.encryptedDataKeys| == 0)
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, key: seq<uint8>, wrappingAlg: EncryptionSuites.EncryptionSuite)
      requires |namespace| < UINT16_LIMIT
      requires wrappingAlg in VALID_ALGORITHMS
      requires wrappingAlg.Valid()
      requires |key| == 16 || |key| == 24 || |key| == 32
      requires |key| == wrappingAlg.keyLen as int
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures wrappingAlgorithm == wrappingAlg
      decreases namespace, name, key, wrappingAlg
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      wrappingAlgorithm := wrappingAlg;
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires Valid()
      requires |iv| == wrappingAlgorithm.ivLen as int
      decreases iv
    {
      keyName + [0, 0, 0, wrappingAlgorithm.tagLen * 8] + [0, 0, 0, wrappingAlgorithm.ivLen] + iv
    }

    method OnEncrypt(input: Crypto.OnEncryptInput) returns (res: Result<Crypto.OnEncryptOutput, string>)
      ensures res.Success? ==> input.materials.encryptionContext == res.value.materials.encryptionContext && input.materials.algorithmSuiteId == res.value.materials.algorithmSuiteId && (input.materials.plaintextDataKey.Some? ==> res.value.materials.plaintextDataKey == input.materials.plaintextDataKey) && input.materials.encryptedDataKeys <= res.value.materials.encryptedDataKeys && input.materials.signingKey == res.value.materials.signingKey
      ensures res.Success? ==> true && var encCtxSerializable: bool := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(input.materials.encryptionContext)); |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1 && encCtxSerializable && wrappingAlgorithm.tagLen as nat <= |res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext| && var encOutput: AESEncryption.EncryptionOutput := DeserializeEDKCiphertext(res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].ciphertext, wrappingAlgorithm.tagLen as nat); true && AESEncryption.EncryptionOutputEncryptedWithAAD(encOutput, EncryptionContext.MapToSeq(input.materials.encryptionContext))
      ensures res.Success? ==> |res.value.materials.encryptedDataKeys| == |input.materials.encryptedDataKeys| + 1 && res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].keyProviderId == keyNamespace && ValidProviderInfo(res.value.materials.encryptedDataKeys[|input.materials.encryptedDataKeys|].keyProviderInfo)
      ensures !EncryptionContext.Serializable(input.materials.encryptionContext) ==> res.Failure?
      decreases input
    {
      :- Need(Valid(), ""Keyring in invalid state"");
      :- Need(ValidEncryptionMaterials(input.materials), ""input encryption materials invalid"");
      reveal EncryptionContext.Serializable();
      var valid := EncryptionContext.CheckSerializable(input.materials.encryptionContext);
      if !valid {
        return Failure(""Unable to serialize encryption context"");
      }
      var materialsWithDataKey := input.materials;
      if materialsWithDataKey.plaintextDataKey.None? {
        var k :- Random.GenerateBytes(AlgorithmSuite.PolymorphIDToInternalID(input.materials.algorithmSuiteId).KeyLength() as int32);
        materialsWithDataKey := Crypto.EncryptionMaterials(encryptionContext := materialsWithDataKey.encryptionContext, algorithmSuiteId := materialsWithDataKey.algorithmSuiteId, signingKey := materialsWithDataKey.signingKey, plaintextDataKey := Some(k), encryptedDataKeys := []);
      }
      var iv :- Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var providerInfo := SerializeProviderInfo(iv);
      var wr := new Streams.ByteWriter();
      var _ :- Serialize.SerializeKVPairs(wr, input.materials.encryptionContext);
      var aad := wr.GetDataWritten();
      assert aad == EncryptionContext.MapToSeq(input.materials.encryptionContext);
      var encryptResult :- AESEncryption.AESEncrypt(wrappingAlgorithm, iv, wrappingKey, materialsWithDataKey.plaintextDataKey.value, aad);
      var encryptedKey := SerializeEDKCiphertext(encryptResult);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure(""Serialized provider info too long."");
      }
      if UINT16_LIMIT <= |encryptedKey| {
        return Failure(""Encrypted data key too long."");
      }
      var edk: Crypto.ValidEncryptedDataKey := Crypto.EncryptedDataKey(keyProviderId := keyNamespace, keyProviderInfo := providerInfo, ciphertext := encryptedKey);
      var edks: seq<Crypto.ValidEncryptedDataKey> := materialsWithDataKey.encryptedDataKeys + [edk];
      var r := Crypto.EncryptionMaterials(encryptionContext := materialsWithDataKey.encryptionContext, algorithmSuiteId := materialsWithDataKey.algorithmSuiteId, signingKey := materialsWithDataKey.signingKey, plaintextDataKey := materialsWithDataKey.plaintextDataKey, encryptedDataKeys := edks);
      assert materialsWithDataKey.encryptedDataKeys == input.materials.encryptedDataKeys;
      assert |edks| == |materialsWithDataKey.encryptedDataKeys| + 1;
      assert r.encryptedDataKeys == edks;
      assert |r.encryptedDataKeys| == |edks|;
      assert |r.encryptedDataKeys| >= |input.materials.encryptedDataKeys|;
      res := Success(Crypto.OnEncryptOutput(materials := r));
    }

    method OnDecrypt(input: Crypto.OnDecryptInput) returns (res: Result<Crypto.OnDecryptOutput, string>)
      ensures Valid() && |input.encryptedDataKeys| == 0 ==> res.Success? && input.materials == res.value.materials
      ensures Valid() && input.materials.plaintextDataKey.Some? ==> res.Success? && input.materials == res.value.materials
      ensures res.Success? ==> input.materials.encryptionContext == res.value.materials.encryptionContext && input.materials.algorithmSuiteId == res.value.materials.algorithmSuiteId && (input.materials.plaintextDataKey.Some? ==> res.value.materials.plaintextDataKey == input.materials.plaintextDataKey) && res.value.materials.verificationKey == input.materials.verificationKey
      ensures res.Success? && input.materials.plaintextDataKey.None? && res.value.materials.plaintextDataKey.Some? ==> var encCtxSerializable: bool := (reveal EncryptionContext.Serializable(); EncryptionContext.Serializable(input.materials.encryptionContext)); encCtxSerializable && AESEncryption.PlaintextDecryptedWithAAD(res.value.materials.plaintextDataKey.value, EncryptionContext.MapToSeq(input.materials.encryptionContext))
      ensures input.materials.plaintextDataKey.None? && !EncryptionContext.Serializable(input.materials.encryptionContext) && (exists i: int :: 0 <= i < |input.encryptedDataKeys| && ShouldDecryptEDK(input.encryptedDataKeys[i])) ==> res.Failure?
      decreases input
    {
      :- Need(Valid(), ""Keyring in invalid state"");
      if input.materials.plaintextDataKey.Some? {
        return Success(Crypto.OnDecryptOutput(materials := input.materials));
      }
      var i := 0;
      while i < |input.encryptedDataKeys|
        invariant forall prevIndex: int :: 0 <= prevIndex < i ==> prevIndex < |input.encryptedDataKeys| && !ShouldDecryptEDK(input.encryptedDataKeys[prevIndex])
        decreases |input.encryptedDataKeys| - i
      {
        if ShouldDecryptEDK(input.encryptedDataKeys[i]) {
          reveal EncryptionContext.Serializable();
          var valid := EncryptionContext.CheckSerializable(input.materials.encryptionContext);
          if !valid {
            return Failure(""Unable to serialize encryption context"");
          }
          var wr := new Streams.ByteWriter();
          var _ :- Serialize.SerializeKVPairs(wr, input.materials.encryptionContext);
          var aad := wr.GetDataWritten();
          assert aad == EncryptionContext.MapToSeq(input.materials.encryptionContext);
          var iv := GetIvFromProvInfo(input.encryptedDataKeys[i].keyProviderInfo);
          var encryptionOutput := DeserializeEDKCiphertext(input.encryptedDataKeys[i].ciphertext, wrappingAlgorithm.tagLen as nat);
          var ptKey :- AESEncryption.AESDecrypt(wrappingAlgorithm, wrappingKey, encryptionOutput.cipherText, encryptionOutput.authTag, iv, aad);
          if AlgorithmSuite.PolymorphIDToInternalID(input.materials.algorithmSuiteId).ValidPlaintextDataKey(ptKey) {
            var r := Crypto.DecryptionMaterials(encryptionContext := input.materials.encryptionContext, algorithmSuiteId := input.materials.algorithmSuiteId, verificationKey := input.materials.verificationKey, plaintextDataKey := Some(ptKey));
            return Success(Crypto.OnDecryptOutput(materials := r));
          } else {
            return Failure(""Decryption failed: bad datakey length."");
          }
        }
        i := i + 1;
      }
      return Success(Crypto.OnDecryptOutput(materials := input.materials));
    }

    predicate method ShouldDecryptEDK(edk: Crypto.EncryptedDataKey)
      decreases edk
    {
      edk.keyProviderId == keyNamespace &&
      ValidProviderInfo(edk.keyProviderInfo) &&
      wrappingAlgorithm.tagLen as int <= |edk.ciphertext|
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
      decreases info
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      info[0 .. |keyName|] == keyName &&
      SeqToUInt32(info[|keyName| .. |keyName| + AUTH_TAG_LEN_LEN]) == 128 &&
      SeqToUInt32(info[|keyName| .. |keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == 12
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
      decreases info
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN..]
    }
  }

  const AUTH_TAG_LEN_LEN := 4
  const IV_LEN_LEN := 4
  const VALID_ALGORITHMS := {EncryptionSuites.AES_GCM_128, EncryptionSuites.AES_GCM_192, EncryptionSuites.AES_GCM_256}

  function method DeserializeEDKCiphertext(ciphertext: seq<uint8>, tagLen: nat): (encOutput: AESEncryption.EncryptionOutput)
    requires tagLen <= |ciphertext|
    ensures |encOutput.authTag| == tagLen
    decreases ciphertext, tagLen
  {
    var encryptedKeyLength: int := |ciphertext| - tagLen as int;
    AESEncryption.EncryptionOutput(ciphertext[..encryptedKeyLength], ciphertext[encryptedKeyLength..])
  }

  function method SerializeEDKCiphertext(encOutput: AESEncryption.EncryptionOutput): (ciphertext: seq<uint8>)
    decreases encOutput
  {
    encOutput.cipherText + encOutput.authTag
  }

  lemma EDKSerializeDeserialize(encOutput: AESEncryption.EncryptionOutput)
    ensures DeserializeEDKCiphertext(SerializeEDKCiphertext(encOutput), |encOutput.authTag|) == encOutput
    decreases encOutput
  {
  }

  lemma EDKDeserializeSerialze(ciphertext: seq<uint8>, tagLen: nat)
    requires tagLen <= |ciphertext|
    ensures SerializeEDKCiphertext(DeserializeEDKCiphertext(ciphertext, tagLen)) == ciphertext
    decreases ciphertext, tagLen
  {
  }
}

module {:extern ""Materials""} Materials {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import AlgorithmSuite = AlgorithmSuite

  import EncryptionContext = EncryptionContext
  datatype EncryptedDataKey = EncryptedDataKey(providerID: UTF8.ValidUTF8Bytes, providerInfo: seq<uint8>, ciphertext: seq<uint8>) {
    predicate Valid()
      decreases this
    {
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }

    static function method ValidWitness(): EncryptedDataKey
    {
      EncryptedDataKey([], [], [])
    }
  }

  type ValidEncryptedDataKey = i: EncryptedDataKey
    | i.Valid()
    witness EncryptedDataKey.ValidWitness()

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext.Map, algorithmSuiteID: AlgorithmSuite.ID, plaintextDataKey: Option<seq<uint8>>, encryptedDataKeys: seq<ValidEncryptedDataKey>, signingKey: Option<seq<uint8>>) {
    predicate Valid()
      decreases this
    {
      (algorithmSuiteID.SignatureType().Some? ==>
        signingKey.Some?) &&
      (plaintextDataKey.Some? ==>
        algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value)) &&
      (plaintextDataKey.None? ==>
        |encryptedDataKeys| == 0)
    }

    predicate Empty()
      decreases this
    {
      plaintextDataKey.None? &&
      |encryptedDataKeys| == 0 &&
      (algorithmSuiteID.SignatureType().Some? ==>
        signingKey.Some?)
    }

    predicate Useable()
      decreases this
    {
      plaintextDataKey.Some? &&
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value) &&
      |encryptedDataKeys| > 0 &&
      (algorithmSuiteID.SignatureType().Some? ==>
        signingKey.Some?)
    }

    predicate Serializable()
      decreases this
    {
      |encryptedDataKeys| > 0 &&
      EncryptionContext.Serializable(encryptionContext)
    }

    static function method ValidWitness(): EncryptionMaterials
    {
      EncryptionMaterials(map[], AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, None, [], Some(seq(32, (i: int) => 0)))
    }

    static function method WithoutDataKeys(encryptionContext: EncryptionContext.Map, algorithmSuiteID: AlgorithmSuite.ID, signingKey: Option<seq<uint8>>): ValidEncryptionMaterials
      requires algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?
      decreases encryptionContext, algorithmSuiteID, signingKey
    {
      var m: EncryptionMaterials := EncryptionMaterials(encryptionContext, algorithmSuiteID, None, [], signingKey);
      assert m.Valid();
      m
    }

    function method WithKeys(newPlaintextDataKey: Option<seq<uint8>>, newEncryptedDataKeys: seq<ValidEncryptedDataKey>): (res: ValidEncryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.Some? ==> newPlaintextDataKey == this.plaintextDataKey
      requires newPlaintextDataKey.Some? ==> this.algorithmSuiteID.ValidPlaintextDataKey(newPlaintextDataKey.value)
      requires newPlaintextDataKey.None? ==> |newEncryptedDataKeys| == 0
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID
      ensures newPlaintextDataKey == res.plaintextDataKey
      ensures this.encryptedDataKeys + newEncryptedDataKeys == res.encryptedDataKeys
      ensures this.signingKey == res.signingKey
      decreases this, newPlaintextDataKey, newEncryptedDataKeys
    {
      var r: EncryptionMaterials := this.(plaintextDataKey := newPlaintextDataKey, encryptedDataKeys := encryptedDataKeys + newEncryptedDataKeys);
      assert r.Valid();
      r
    }
  }

  type ValidEncryptionMaterials = i: EncryptionMaterials
    | i.Valid()
    witness EncryptionMaterials.ValidWitness()

  type EmptyEncryptionMaterials = i: EncryptionMaterials
    | i.Empty()
    witness *

  type UseableEncryptionMaterials = i: EncryptionMaterials
    | i.Useable()
    witness *

  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: EncryptionContext.Map, plaintextDataKey: Option<seq<uint8>>, verificationKey: Option<seq<uint8>>) {
    predicate Valid()
      decreases this
    {
      (plaintextDataKey.Some? ==>
        algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value)) &&
      (algorithmSuiteID.SignatureType().Some? ==>
        verificationKey.Some?)
    }

    predicate Pending()
      decreases this
    {
      plaintextDataKey.None? &&
      (algorithmSuiteID.SignatureType().Some? ==>
        verificationKey.Some?)
    }

    predicate Complete()
      decreases this
    {
      plaintextDataKey.Some? &&
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.value) &&
      (algorithmSuiteID.SignatureType().Some? ==>
        verificationKey.Some?)
    }

    static function method ValidWitness(): DecryptionMaterials
    {
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, map[], Some(seq(32, (i: int) => 0)), Some(seq(32, (i: int) => 0)))
    }

    static function method WithoutPlaintextDataKey(encryptionContext: EncryptionContext.Map, algorithmSuiteID: AlgorithmSuite.ID, verificationKey: Option<seq<uint8>>): ValidDecryptionMaterials
      requires algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?
      decreases encryptionContext, algorithmSuiteID, verificationKey
    {
      var m: DecryptionMaterials := DecryptionMaterials(algorithmSuiteID, encryptionContext, None, verificationKey);
      assert m.Valid();
      m
    }

    function method WithPlaintextDataKey(plaintextDataKey: seq<uint8>): (res: ValidDecryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.None?
      requires algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID
      ensures res.plaintextDataKey.Some?
      ensures this.verificationKey == res.verificationKey
      decreases this, plaintextDataKey
    {
      var m: DecryptionMaterials := this.(plaintextDataKey := Some(plaintextDataKey));
      assert m.Valid();
      m
    }
  }

  type PendingDecryptionMaterials = i: DecryptionMaterials
    | i.Pending()
    witness *

  type CompleteDecryptionMaterials = i: DecryptionMaterials
    | i.Complete()
    witness *

  type ValidDecryptionMaterials = i: DecryptionMaterials
    | i.Valid()
    witness DecryptionMaterials.ValidWitness()

  datatype EncryptionMaterialsRequest = EncryptionMaterialsRequest(encryptionContext: EncryptionContext.Map, algorithmSuiteID: Option<AlgorithmSuite.ID>, plaintextLength: Option<nat>)

  datatype DecryptionMaterialsRequest = DecryptionMaterialsRequest(algorithmSuiteID: AlgorithmSuite.ID, encryptedDataKeys: seq<ValidEncryptedDataKey>, encryptionContext: EncryptionContext.Map) {
    predicate Valid()
      decreases this
    {
      |encryptedDataKeys| > 0
    }

    static function method ValidWitness(): DecryptionMaterialsRequest
    {
      DecryptionMaterialsRequest(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, [EncryptedDataKey.ValidWitness()], map[])
    }
  }

  type ValidDecryptionMaterialsRequest = i: DecryptionMaterialsRequest
    | i.Valid()
    witness DecryptionMaterialsRequest.ValidWitness()

  const EC_PUBLIC_KEY_FIELD: UTF8.ValidUTF8Bytes := var s: seq<uint8> := [97, 119, 115, 45, 99, 114, 121, 112, 116, 111, 45, 112, 117, 98, 108, 105, 99, 45, 107, 101, 121]; assert UTF8.ValidUTF8Range(s, 0, 21); s
  const RESERVED_KEY_VALUES := {EC_PUBLIC_KEY_FIELD}
}

module MessageBody {

  export
    provides EncryptMessageBody, DecryptFramedMessageBody, DecryptNonFramedMessageBody, Wrappers, UInt, Msg, AlgorithmSuite, Materials, Streams, FramesToSequence, FrameToSequence, ValidFrames, FramesEncryptPlaintext, AESEncryption, DecryptedWithKey
    reveals Frame, Frame.Valid, SeqWithGhostFrames


  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import AlgorithmSuite = AlgorithmSuite

  import Msg = MessageHeader

  import AESEncryption = AESEncryption

  import Materials = Materials

  import Streams = Streams

  import EncryptionSuites = EncryptionSuites

  import UTF8 = UTF8
  datatype BodyAADContent = AADRegularFrame | AADFinalFrame | AADSingleBlock

  datatype Frame = RegularFrame(seqNum: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) | FinalFrame(seqNum: uint32, iv: seq<uint8>, encContent: seq<uint8>, authTag: seq<uint8>) {
    predicate Valid()
      decreases this
    {
      |encContent| < UINT32_LIMIT
    }
  }

  datatype SeqWithGhostFrames = SeqWithGhostFrames(sequence: seq<uint8>, ghost frames: seq<Frame>)

  datatype FrameWithGhostSeq = FrameWithGhostSeq(frame: Frame, ghost sequence: seq<uint8>)

  predicate ValidFrames(frames: seq<Frame>)
    decreases frames
  {
    0 < |frames| < UINT32_LIMIT &&
    forall i: int | 0 <= i < |frames| :: 
      ghost var frame: Frame := frames[i]; frame.Valid() && (if i == |frames| - 1 then frame.FinalFrame? else frame.RegularFrame?) && frame.seqNum as int == i + START_SEQUENCE_NUMBER as int && forall j: int | i < j < |frames| :: frame.iv != frames[j].iv
  }

  const BODY_AAD_CONTENT_REGULAR_FRAME: string := ""AWSKMSEncryptionClient Frame""
  const BODY_AAD_CONTENT_FINAL_FRAME: string := ""AWSKMSEncryptionClient Final Frame""
  const BODY_AAD_CONTENT_SINGLE_BLOCK: string := ""AWSKMSEncryptionClient Single Block""

  function method BodyAADContentTypeString(bc: BodyAADContent): string
    decreases bc
  {
    match bc
    case AADRegularFrame() =>
      BODY_AAD_CONTENT_REGULAR_FRAME
    case AADFinalFrame() =>
      BODY_AAD_CONTENT_FINAL_FRAME
    case AADSingleBlock() =>
      BODY_AAD_CONTENT_SINGLE_BLOCK
  }

  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 4294967295
  const NONFRAMED_SEQUENCE_NUMBER: uint32 := 1

  function method IVSeq(algorithmSuiteID: AlgorithmSuite.ID, sequenceNumber: uint32): seq<uint8>
    decreases algorithmSuiteID, sequenceNumber
  {
    seq(algorithmSuiteID.IVLength() - 4, (_: int) => 0) + UInt32ToSeq(sequenceNumber)
  }

  lemma IVSeqDistinct(algorithmSuiteID: AlgorithmSuite.ID, m: uint32, n: uint32)
    requires m != n
    ensures IVSeq(algorithmSuiteID, m) != IVSeq(algorithmSuiteID, n)
    decreases algorithmSuiteID, m, n
  {
    ghost var paddingLength := algorithmSuiteID.IVLength() - 4;
    assert IVSeq(algorithmSuiteID, m)[paddingLength..] == UInt32ToSeq(m);
    assert IVSeq(algorithmSuiteID, n)[paddingLength..] == UInt32ToSeq(n);
    UInt32SeqSerializeDeserialize(m);
    UInt32SeqSerializeDeserialize(n);
  }

  function FramesToSequence(frames: seq<Frame>): seq<uint8>
    requires forall frame: Frame | frame in frames :: frame.Valid()
    decreases frames
  {
    if frames == [] then
      []
    else
      FramesToSequence(frames[..|frames| - 1]) + FrameToSequence(frames[|frames| - 1])
  }

  lemma /*{:_induction frames}*/ ExtendFramesToSequence(frames: seq<Frame>, frame: Frame)
    requires |frames| < UINT32_LIMIT - 1
    requires forall frame: Frame | frame in frames :: frame.Valid()
    requires frame.Valid()
    ensures FramesToSequence(frames + [frame]) == FramesToSequence(frames) + FrameToSequence(frame)
    decreases frames, frame
  {
  }

  function FrameToSequence(frame: Frame): (res: seq<uint8>)
    requires frame.Valid()
    ensures match frame { case RegularFrame(_mcc#0, _mcc#1, _mcc#2, _mcc#3) => (var authTag: seq<uint8> := _mcc#3; var encContent: seq<uint8> := _mcc#2; var iv: seq<uint8> := _mcc#1; 4 + |iv| + |encContent| + |authTag| == |res|) case FinalFrame(_mcc#4, _mcc#5, _mcc#6, _mcc#7) => var authTag: seq<uint8> := _mcc#7; var encContent: seq<uint8> := _mcc#6; var iv: seq<uint8> := _mcc#5; var seqNum: uint32 := _mcc#4; 4 + 4 + |iv| + 4 + |encContent| + |authTag| == |res| }
    decreases frame
  {
    match frame
    case RegularFrame(seqNum, iv, encContent, authTag) =>
      var seqNumSeq := UInt32ToSeq(seqNum);
      seqNumSeq + iv + encContent + authTag
    case FinalFrame(seqNum, iv, encContent, authTag) =>
      var seqNumEndSeq := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
      var seqNumSeq := UInt32ToSeq(seqNum);
      var encContentLengthSeq := UInt32ToSeq(|encContent| as uint32);
      seqNumEndSeq + seqNumSeq + iv + encContentLengthSeq + encContent + authTag
  }

  predicate FramesEncryptPlaintext(frames: seq<Frame>, plaintext: seq<uint8>)
    decreases frames, plaintext
  {
    exists plaintextSeg: seq<seq<uint8>> :: 
      FramesEncryptPlaintextSegments(frames, plaintextSeg) &&
      SumPlaintextSegments(plaintextSeg) == plaintext
  }

  predicate FramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>)
    decreases frames, plaintextSeg
  {
    if |frames| != |plaintextSeg| then
      false
    else if frames == [] then
      true
    else
      FramesEncryptPlaintextSegments(frames[..|frames| - 1], plaintextSeg[..|frames| - 1]) && AESEncryption.CiphertextGeneratedWithPlaintext(frames[|frames| - 1].encContent, plaintextSeg[|frames| - 1])
  }

  lemma /*{:_induction frames, plaintextSeg}*/ ExtendFramesEncryptPlaintextSegments(frames: seq<Frame>, plaintextSeg: seq<seq<uint8>>, frame: Frame, plaintextFrame: seq<uint8>)
    requires FramesEncryptPlaintextSegments(frames, plaintextSeg)
    requires AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintextFrame)
    ensures FramesEncryptPlaintextSegments(frames + [frame], plaintextSeg + [plaintextFrame])
    decreases frames, plaintextSeg, frame, plaintextFrame
  {
  }

  function SumPlaintextSegments(plaintextSeg: seq<seq<uint8>>): seq<uint8>
    decreases plaintextSeg
  {
    if plaintextSeg == [] then
      []
    else
      SumPlaintextSegments(plaintextSeg[..|plaintextSeg| - 1]) + plaintextSeg[|plaintextSeg| - 1]
  }

  lemma /*{:_induction plaintextSeg}*/ ExtendSumPlaintextSegments(plaintextSeg: seq<seq<uint8>>, plaintextFrame: seq<uint8>)
    ensures SumPlaintextSegments(plaintextSeg + [plaintextFrame]) == SumPlaintextSegments(plaintextSeg) + plaintextFrame
    decreases plaintextSeg, plaintextFrame
  {
  }

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID)
      returns (result: Result<SeqWithGhostFrames, string>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    ensures match result { case Success(_mcc#0) => (var seqWithGhostFrames := _mcc#0; var frames := seqWithGhostFrames.frames; ValidFrames(frames) && (forall frame | frame in frames :: frame.Valid()) && (forall frame: Frame | frame in frames :: |frame.iv| == algorithmSuiteID.IVLength()) && FramesToSequence(frames) == seqWithGhostFrames.sequence && FramesEncryptPlaintext(frames, plaintext) && forall frame: Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, key)) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases plaintext, frameLength, messageID, key, algorithmSuiteID
  {
    var body := [];
    var n: int, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    ghost var frames: seq<Frame> := [];
    ghost var plaintextSeg := [];
    while n + frameLength < |plaintext|
      invariant |plaintext| != 0 ==> 0 <= n < |plaintext|
      invariant |plaintext| == 0 ==> 0 == n
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      invariant |frames| == (sequenceNumber - START_SEQUENCE_NUMBER) as int
      invariant forall i: int | 0 <= i < |frames| :: var frame: Frame := frames[i]; frame.Valid() && frame.RegularFrame? && frame.seqNum as int == i + START_SEQUENCE_NUMBER as int
      invariant forall i: int | 0 <= i < |frames| :: frames[i].iv == IVSeq(algorithmSuiteID, frames[i].seqNum)
      invariant FramesToSequence(frames) == body
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg)
      invariant SumPlaintextSegments(plaintextSeg) == plaintext[..n]
      invariant forall frame: Frame | frame in frames :: AESEncryption.EncryptedWithKey(frame.encContent, key)
      decreases |plaintext| - (n + frameLength)
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure(""too many frames"");
      }
      var plaintextFrame := plaintext[n .. n + frameLength];
      var regularFrame, frame := EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      if regularFrame.IsFailure() {
        return regularFrame.PropagateFailure();
      }
      assert frame.iv == IVSeq(algorithmSuiteID, sequenceNumber);
      ExtendFramesToSequence(frames, frame);
      ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, frame, plaintextFrame);
      ExtendSumPlaintextSegments(plaintextSeg, plaintextFrame);
      frames := frames + [frame];
      body := body + regularFrame.Extract();
      plaintextSeg := plaintextSeg + [plaintextFrame];
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
      assert SumPlaintextSegments(plaintextSeg) == plaintext[..n];
    }
    var finalFrameResult, finalFrame := EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    if finalFrameResult.IsFailure() {
      return finalFrameResult.PropagateFailure();
    }
    var finalFrameSequence := finalFrameResult.Extract();
    assert finalFrame.iv == IVSeq(algorithmSuiteID, sequenceNumber);
    ExtendFramesToSequence(frames, finalFrame);
    ExtendFramesEncryptPlaintextSegments(frames, plaintextSeg, finalFrame, plaintext[n..]);
    ExtendSumPlaintextSegments(plaintextSeg, plaintext[n..]);
    frames := frames + [finalFrame];
    body := body + finalFrameSequence;
    plaintextSeg := plaintextSeg + [plaintext[n..]];
    assert ValidFrames(frames) by {
      forall i: int, j: int | 0 <= i < j < |frames|
        ensures frames[i].iv != frames[j].iv
      {
        assert frames[i].seqNum as int == i + START_SEQUENCE_NUMBER as int;
        assert frames[j].seqNum as int == j + START_SEQUENCE_NUMBER as int;
        assert frames[i].iv == IVSeq(algorithmSuiteID, frames[i].seqNum);
        assert frames[j].iv == IVSeq(algorithmSuiteID, frames[j].seqNum);
        IVSeqDistinct(algorithmSuiteID, frames[i].seqNum, frames[j].seqNum);
      }
    }
    result := Success(SeqWithGhostFrames(body, frames));
  }

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, ghost frameLength: int, messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>, string>, ghost regFrame: Frame)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res { case Success(_mcc#0) => (var resultSuccess := _mcc#0; 4 + algorithmSuiteID.IVLength() + algorithmSuiteID.TagLength() + frameLength == |resultSuccess| && var iv := IVSeq(algorithmSuiteID, sequenceNumber); var encContent := resultSuccess[4 + algorithmSuiteID.IVLength() .. 4 + algorithmSuiteID.IVLength() + frameLength]; var authTag := resultSuccess[4 + algorithmSuiteID.IVLength() + frameLength..]; var frame := RegularFrame(sequenceNumber, iv, encContent, authTag); frame == regFrame && FrameToSequence(regFrame) == resultSuccess && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext) && AESEncryption.EncryptedWithKey(frame.encContent, key)) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases algorithmSuiteID, key, frameLength, messageID, plaintext, sequenceNumber
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := IVSeq(algorithmSuiteID, sequenceNumber);
    var aad := BodyAAD(messageID, AADRegularFrame, sequenceNumber, |plaintext| as uint64);
    var encryptionOutputResult := AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      regFrame := RegularFrame(0, [], [], []);
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    ghost var frame := RegularFrame(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    return Success(unauthenticatedFrame), frame;
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>, string>, ghost finalFrame: Frame)
    requires |key| == algorithmSuiteID.KeyLength()
    requires START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires 0 <= |plaintext| < UINT32_LIMIT
    requires 0 < frameLength < UINT32_LIMIT
    requires |plaintext| <= frameLength
    requires 4 <= algorithmSuiteID.IVLength()
    ensures match res { case Success(_mcc#0) => (var resultSuccess := _mcc#0; 4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() <= |resultSuccess| <= 4 + 4 + algorithmSuiteID.IVLength() + 4 + algorithmSuiteID.TagLength() + frameLength && var contentLength: uint32 := SeqToUInt32(resultSuccess[4 + 4 + algorithmSuiteID.IVLength() .. 4 + 4 + algorithmSuiteID.IVLength() + 4]); |resultSuccess| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + contentLength as int + algorithmSuiteID.TagLength() && resultSuccess[..4] == UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER) && |plaintext| == SeqToUInt32(resultSuccess[4 + 4 + algorithmSuiteID.IVLength() .. 4 + 4 + algorithmSuiteID.IVLength() + 4]) as int && var iv := IVSeq(algorithmSuiteID, sequenceNumber); var encContent := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4..][..|plaintext|]; var authTag := resultSuccess[4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext|..]; var frame := FinalFrame(sequenceNumber, iv, encContent, authTag); FrameToSequence(frame) == resultSuccess && finalFrame == frame && AESEncryption.CiphertextGeneratedWithPlaintext(frame.encContent, plaintext) && AESEncryption.EncryptedWithKey(frame.encContent, key)) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases algorithmSuiteID, key, frameLength, messageID, plaintext, sequenceNumber
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;
    var iv := IVSeq(algorithmSuiteID, sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);
    var aad := BodyAAD(messageID, AADFinalFrame, sequenceNumber, |plaintext| as uint64);
    var encryptionOutputResult := AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    if encryptionOutputResult.IsFailure() {
      res := encryptionOutputResult.PropagateFailure();
      finalFrame := RegularFrame(0, [], [], []);
      return;
    }
    var encryptionOutput := encryptionOutputResult.Extract();
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    assert |plaintext| == |encryptionOutput.cipherText|;
    ghost var frame := FinalFrame(sequenceNumber, iv, encryptionOutput.cipherText, encryptionOutput.authTag);
    finalFrame := frame;
    assert FrameToSequence(frame) == unauthenticatedFrame;
    assert |plaintext| == SeqToUInt32(unauthenticatedFrame[4 + 4 + algorithmSuiteID.IVLength() .. 4 + 4 + algorithmSuiteID.IVLength() + 4]) as int;
    assert |unauthenticatedFrame| == 4 + 4 + algorithmSuiteID.IVLength() + 4 + |plaintext| + algorithmSuiteID.TagLength();
    assert unauthenticatedFrame[4 + 4 + algorithmSuiteID.IVLength() + 4..][..|plaintext|] == encryptionOutput.cipherText;
    return Success(unauthenticatedFrame), finalFrame;
  }

  method DecryptFramedMessageBody(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID)
      returns (res: Result<seq<uint8>, string>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    ensures match res { case Success(_mcc#0) => (var plaintext := _mcc#0; old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data| && exists frames: seq<Frame> | |frames| < UINT32_LIMIT && (forall frame | frame in frames :: frame.Valid()) && FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] :: true && FramesEncryptPlaintext(frames, plaintext)) case Failure(_mcc#1) => true }
    decreases rd, algorithmSuiteID, key, frameLength, messageID
  {
    var plaintext := [];
    var n: uint32 := 1;
    ghost var frames: seq<Frame> := [];
    ghost var plaintextSeg: seq<seq<uint8>> := [];
    while true
      invariant rd.Valid()
      invariant n as int - 1 == |frames|
      invariant n <= ENDFRAME_SEQUENCE_NUMBER
      invariant forall frame: Frame | frame in frames :: frame.Valid()
      invariant old(rd.reader.pos) <= rd.reader.pos <= |rd.reader.data|
      invariant FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos]
      invariant rd.Valid()
      invariant FramesEncryptPlaintextSegments(frames, plaintextSeg)
      invariant SumPlaintextSegments(plaintextSeg) == plaintext
      invariant DecryptedSegmentsWithKey(key, plaintextSeg)
      invariant plaintext == SumPlaintextSegments(plaintextSeg)
      decreases ENDFRAME_SEQUENCE_NUMBER - n
    {
      var frameWithGhostSeq :- DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, n);
      assert |frameWithGhostSeq.sequence| < UINT32_LIMIT;
      var decryptedFrame := frameWithGhostSeq.frame;
      ghost var ciphertext := frameWithGhostSeq.sequence;
      assert |ciphertext| < UINT32_LIMIT;
      ghost var encryptedFrame := if decryptedFrame.FinalFrame? then FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag) else RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag);
      assert encryptedFrame.Valid();
      frames := frames + [encryptedFrame];
      var (decryptedFramePlaintext, final) := (decryptedFrame.encContent, decryptedFrame.FinalFrame?);

      plaintext := plaintext + decryptedFramePlaintext;
      plaintextSeg := plaintextSeg + [decryptedFramePlaintext];
      if final {
        assert FramesEncryptPlaintextSegments(frames, plaintextSeg);
        assert SumPlaintextSegments(plaintextSeg) == plaintext;
        break;
      }
      n := n + 1;
    }
    assert |frames| < UINT32_LIMIT;
    assert forall frame: Frame | frame in frames :: frame.Valid();
    assert FramesToSequence(frames) == rd.reader.data[old(rd.reader.pos) .. rd.reader.pos];
    return Success(plaintext);
  }

  method DecryptFrame(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID, expectedSequenceNumber: uint32)
      returns (res: Result<FrameWithGhostSeq, string>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd.reader`pos
    ensures rd.Valid()
    ensures match res { case Success(_mcc#0) => (var frameWithGhostSeq := _mcc#0; expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> frameWithGhostSeq.frame.FinalFrame?) case Failure(_mcc#1) => true }
    ensures res.Success? ==> |res.value.sequence| < UINT32_LIMIT
    ensures match res { case Success(_mcc#2) => (var frameWithGhostSeq := _mcc#2; true && var decryptedFrame := frameWithGhostSeq.frame; var ciphertext := frameWithGhostSeq.sequence; var final := decryptedFrame.FinalFrame?; decryptedFrame.Valid() && old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data| && AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, decryptedFrame.encContent) && AESEncryption.DecryptedWithKey(key, decryptedFrame.encContent) && var encryptedFrame := if decryptedFrame.FinalFrame? then FinalFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag) else RegularFrame(decryptedFrame.seqNum, decryptedFrame.iv, ciphertext, decryptedFrame.authTag); rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == FrameToSequence(encryptedFrame) && AESEncryption.CiphertextGeneratedWithPlaintext(encryptedFrame.encContent, decryptedFrame.encContent)) case Failure(_mcc#3) => true }
    decreases rd, algorithmSuiteID, key, frameLength, messageID, expectedSequenceNumber
  {
    var final := false;
    var sequenceNumber :- rd.ReadUInt32();
    ghost var frameSerialization := UInt32ToSeq(sequenceNumber);
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
      frameSerialization := frameSerialization + UInt32ToSeq(sequenceNumber);
      assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    }
    if sequenceNumber != expectedSequenceNumber {
      return Failure(""unexpected frame sequence number"");
    }
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    frameSerialization := frameSerialization + iv;
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
      if len > frameLength as uint32 {
        return Failure(""Final frame too long"");
      }
      frameSerialization := frameSerialization + UInt32ToSeq(len);
    }
    var aad := BodyAAD(messageID, if final then AADFinalFrame else AADRegularFrame, sequenceNumber, len as uint64);
    var ciphertext :- rd.ReadBytes(len as nat);
    frameSerialization := frameSerialization + ciphertext;
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    frameSerialization := frameSerialization + authTag;
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    assert AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, plaintext);
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    var frame := if final then FinalFrame(sequenceNumber, iv, plaintext, authTag) else RegularFrame(sequenceNumber, iv, plaintext, authTag);
    ghost var encryptedFrame := if final then FinalFrame(sequenceNumber, iv, ciphertext, authTag) else RegularFrame(sequenceNumber, iv, ciphertext, authTag);
    assert frameSerialization == FrameToSequence(encryptedFrame);
    assert !final ==> frameSerialization[..4] == rd.reader.data[old(rd.reader.pos)..][..4];
    assert !final ==> frameSerialization[4..][..algorithmSuiteID.IVLength()] == rd.reader.data[old(rd.reader.pos)..][4..][..algorithmSuiteID.IVLength()];
    assert !final ==> frameSerialization[4 + algorithmSuiteID.IVLength()..][..frameLength] == rd.reader.data[old(rd.reader.pos)..][4 + algorithmSuiteID.IVLength()..][..frameLength];
    assert !final ==> frameSerialization[4 + frameLength + algorithmSuiteID.IVLength()..] == rd.reader.data[old(rd.reader.pos)..][4 + frameLength + algorithmSuiteID.IVLength()..][..algorithmSuiteID.TagLength()];
    assert rd.reader.data[old(rd.reader.pos) .. rd.reader.pos] == frameSerialization;
    assert old(rd.reader.pos) < rd.reader.pos <= |rd.reader.data|;
    return Success(FrameWithGhostSeq(frame, ciphertext));
  }

  method BodyAAD(messageID: seq<uint8>, bc: BodyAADContent, sequenceNumber: uint32, length: uint64)
      returns (aad: seq<uint8>)
    decreases messageID, bc, sequenceNumber, length
  {
    var contentAAD := UTF8.Encode(BodyAADContentTypeString(bc));
    aad := messageID + contentAAD.value + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(ciphertext: seq<uint8>, authTag: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, string>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    requires |authTag| == algorithmSuiteID.TagLength()
    ensures res.Success? ==> AESEncryption.CiphertextGeneratedWithPlaintext(ciphertext, res.value)
    ensures res.Success? ==> |ciphertext| == |res.value|
    ensures res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value)
    decreases ciphertext, authTag, algorithmSuiteID, iv, key, aad
  {
    var encAlg := algorithmSuiteID.EncryptionSuite();
    res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
    assert res.Success? ==> AESEncryption.DecryptedWithKey(key, res.value);
  }

  predicate DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)
    decreases key, plaintext
  {
    if AESEncryption.DecryptedWithKey(key, plaintext) then
      true
    else
      exists plaintextSeg: seq<seq<uint8>> | SumPlaintextSegments(plaintextSeg) == plaintext :: DecryptedSegmentsWithKey(key, plaintextSeg)
  }

  predicate DecryptedSegmentsWithKey(key: seq<uint8>, plaintextSeg: seq<seq<uint8>>)
    decreases key, plaintextSeg
  {
    if plaintextSeg == [] then
      true
    else
      DecryptedSegmentsWithKey(key, plaintextSeg[..|plaintextSeg| - 1]) && AESEncryption.DecryptedWithKey(key, plaintextSeg[|plaintextSeg| - 1])
  }

  method DecryptNonFramedMessageBody(rd: Streams.ByteReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, messageID: Msg.MessageID)
      returns (res: Result<seq<uint8>, string>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    modifies rd.reader`pos
    ensures rd.Valid()
    decreases rd, algorithmSuiteID, key, messageID
  {
    var iv :- rd.ReadBytes(algorithmSuiteID.IVLength());
    var contentLength :- rd.ReadUInt64();
    var ciphertext :- rd.ReadBytes(contentLength as nat);
    var authTag :- rd.ReadBytes(algorithmSuiteID.TagLength());
    var aad := BodyAAD(messageID, AADSingleBlock, NONFRAMED_SEQUENCE_NUMBER, contentLength);
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    return Success(plaintext);
  }
}

module {:extern ""MessageHeader""} MessageHeader {

  import Crypto = Aws.Crypto

  import AlgorithmSuite = AlgorithmSuite

  import Sets = Sets

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import EncryptionContext = EncryptionContext

  import Materials = Materials

  import UTF8 = UTF8

  import AESEncryption = AESEncryption
  datatype Header = Header(body: HeaderBody, auth: HeaderAuthentication) {
    predicate Valid()
      decreases this
    {
      body.Valid() &&
      |auth.iv| == body.algorithmSuiteID.IVLength() &&
      |auth.authenticationTag| == body.algorithmSuiteID.TagLength()
    }
  }

  type Version = x: uint8
    | x == VERSION_1
    witness VERSION_1

  type Type = x: uint8
    | x == TYPE_CUSTOMER_AED
    witness TYPE_CUSTOMER_AED

  type MessageID = x: seq<uint8>
    | |x| == MESSAGE_ID_LEN
    witness [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

  datatype ContentType = NonFramed | Framed

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Crypto.EncryptedDataKey>) {
    predicate Valid()
      decreases this
    {
      0 < |entries| < UINT16_LIMIT &&
      forall i: int :: 
        0 <= i < |entries| ==>
          entries[i].Valid()
    }
  }

  datatype HeaderBody = HeaderBody(version: Version, typ: Type, algorithmSuiteID: AlgorithmSuite.ID, messageID: MessageID, aad: EncryptionContext.Map, encryptedDataKeys: EncryptedDataKeys, contentType: ContentType, ivLength: uint8, frameLength: uint32) {
    predicate Valid()
      decreases this
    {
      EncryptionContext.Serializable(aad) &&
      encryptedDataKeys.Valid() &&
      algorithmSuiteID.IVLength() == ivLength as nat &&
      ValidFrameLength(frameLength, contentType)
    }
  }

  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)

  const VERSION_1: uint8 := 1
  const TYPE_CUSTOMER_AED: uint8 := 128
  const MESSAGE_ID_LEN := 16
  const Reserved: seq<uint8> := [0, 0, 0, 0]

  function method ContentTypeToUInt8(contentType: ContentType): uint8
    decreases contentType
  {
    match contentType
    case NonFramed() =>
      1
    case Framed() =>
      2
  }

  function method UInt8ToContentType(x: uint8): Option<ContentType>
    decreases x
  {
    if x == 1 then
      Some(NonFramed)
    else if x == 2 then
      Some(Framed)
    else
      None
  }

  lemma ContentTypeConversionsCorrect(contentType: ContentType, x: uint8)
    ensures UInt8ToContentType(ContentTypeToUInt8(contentType)) == Some(contentType)
    ensures ghost var opt: Option<ContentType> := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.value) == x
    decreases contentType, x
  {
  }

  predicate HeaderAuthenticationMatchesHeaderBody(headerAuthentication: HeaderAuthentication, headerBody: HeaderBody)
    requires headerBody.Valid()
    decreases headerAuthentication, headerBody
  {
    ghost var serializedHeaderBody: seq<uint8> := (reveal HeaderBodyToSeq(); HeaderBodyToSeq(headerBody));
    headerAuthentication.iv == seq(headerBody.algorithmSuiteID.IVLength(), (_: int) => 0) &&
    exists encryptionOutput: EncryptionOutput | AESEncryption.EncryptionOutputEncryptedWithAAD(encryptionOutput, serializedHeaderBody) && AESEncryption.CiphertextGeneratedWithPlaintext(encryptionOutput.cipherText, []) :: 
      encryptionOutput.authTag == headerAuthentication.authenticationTag
  }

  predicate ValidFrameLength(frameLength: uint32, contentType: ContentType)
    decreases frameLength, contentType
  {
    match contentType
    case NonFramed() =>
      frameLength == 0
    case Framed() =>
      frameLength != 0
  }

  function {:opaque} {:fuel 0, 0} HeaderBodyToSeq(hb: HeaderBody): seq<uint8>
    requires hb.Valid()
    decreases hb
  {
    [hb.version as uint8] + [hb.typ as uint8] + UInt16ToSeq(hb.algorithmSuiteID as uint16) + hb.messageID + EncryptionContext.MapToLinear(hb.aad) + EDKsToSeq(hb.encryptedDataKeys) + [ContentTypeToUInt8(hb.contentType)] + Reserved + [hb.ivLength] + UInt32ToSeq(hb.frameLength)
  }

  function EDKsToSeq(encryptedDataKeys: EncryptedDataKeys): seq<uint8>
    requires encryptedDataKeys.Valid()
    decreases encryptedDataKeys
  {
    ghost var n: int := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) + EDKEntriesToSeq(encryptedDataKeys.entries, 0, n)
  }

  function EDKEntriesToSeq(entries: seq<Crypto.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i: int :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
    decreases entries, lo, hi
  {
    if lo == hi then
      []
    else
      EDKEntriesToSeq(entries, lo, hi - 1) + EDKEntryToSeq(entries[hi - 1])
  }

  lemma /*{:_induction entriesHead, entriesTail, lo, hi}*/ EDKEntriesToSeqInductiveStep(entriesHead: seq<Crypto.EncryptedDataKey>, entriesTail: seq<Crypto.EncryptedDataKey>, lo: nat, hi: nat)
    requires ghost var entries: seq<Crypto.EncryptedDataKey> := entriesHead + entriesTail; forall i: int :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entriesHead|
    ensures forall i: int :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid()
    ensures ghost var entries: seq<Crypto.EncryptedDataKey> := entriesHead + entriesTail; EDKEntriesToSeq(entriesHead + entriesTail, lo, hi) == EDKEntriesToSeq(entriesHead, lo, hi)
    decreases entriesHead, entriesTail, lo, hi
  {
    assert forall i: int :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid() by {
      if !forall i: int :: 0 <= i < |entriesHead| ==> entriesHead[i].Valid() {
        ghost var entry :| entry in entriesHead && !entry.Valid();
        assert entry in entriesHead + entriesTail;
        assert false;
      }
    }
  }

  function method EDKEntryToSeq(edk: Crypto.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
    decreases edk
  {
    UInt16ToSeq(|edk.keyProviderId| as uint16) + edk.keyProviderId + UInt16ToSeq(|edk.keyProviderInfo| as uint16) + edk.keyProviderInfo + UInt16ToSeq(|edk.ciphertext| as uint16) + edk.ciphertext
  }

  predicate {:opaque} {:fuel 0, 0} IsSerializationOfHeaderBody(sequence: seq<uint8>, hb: HeaderBody)
    requires hb.Valid()
    decreases sequence, hb
  {
    exists serializedAAD: seq<uint8> | EncryptionContext.LinearSeqToMap(serializedAAD, hb.aad) :: 
      IsSerializationOfHeaderBodyAux(sequence, hb, serializedAAD)
  }

  predicate IsSerializationOfHeaderBodyAux(sequence: seq<uint8>, hb: HeaderBody, serializedAAD: seq<uint8>)
    requires hb.Valid() && EncryptionContext.LinearSeqToMap(serializedAAD, hb.aad)
    decreases sequence, hb, serializedAAD
  {
    sequence == [hb.version as uint8] + [hb.typ as uint8] + UInt16ToSeq(hb.algorithmSuiteID as uint16) + hb.messageID + serializedAAD + EDKsToSeq(hb.encryptedDataKeys) + [ContentTypeToUInt8(hb.contentType)] + Reserved + [hb.ivLength] + UInt32ToSeq(hb.frameLength)
  }

  lemma IsSerializationOfHeaderBodyDuality(hb: HeaderBody)
    requires hb.Valid()
    ensures IsSerializationOfHeaderBody(HeaderBodyToSeq(hb), hb)
    decreases hb
  {
    reveal HeaderBodyToSeq(), IsSerializationOfHeaderBody();
    EncryptionContext.MapToLinearIsDualLinearSeqToMap(hb.aad);
  }
}

module Serialize {

  import Msg = MessageHeader

  import EncryptionContext = EncryptionContext

  import AlgorithmSuite = AlgorithmSuite

  import Streams = Streams

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import Sets = Sets
  method SerializeHeaderBody(wr: Streams.ByteWriter, hb: Msg.HeaderBody) returns (ret: Result<nat, string>)
    requires wr.Valid() && hb.Valid()
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret { case Success(_mcc#0) => (var totalWritten := _mcc#0; var serHb := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(hb)); var initLen := old(wr.GetSizeWritten()); totalWritten == |serHb| && initLen + totalWritten == wr.GetSizeWritten() && serHb == wr.GetDataWritten()[initLen .. initLen + totalWritten]) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases wr, hb
  {
    var totalWritten := 0;
    var len := wr.WriteByte(hb.version as uint8);
    totalWritten := totalWritten + len;
    len := wr.WriteByte(hb.typ as uint8);
    totalWritten := totalWritten + len;
    len := wr.WriteUInt16(hb.algorithmSuiteID as uint16);
    totalWritten := totalWritten + len;
    len := wr.WriteBytes(hb.messageID);
    totalWritten := totalWritten + len;
    len :- SerializeAAD(wr, hb.aad);
    totalWritten := totalWritten + len;
    len := SerializeEDKs(wr, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;
    var contentType := Msg.ContentTypeToUInt8(hb.contentType);
    len := wr.WriteByte(contentType);
    totalWritten := totalWritten + len;
    len := wr.WriteBytes(Msg.Reserved);
    totalWritten := totalWritten + len;
    len := wr.WriteByte(hb.ivLength);
    totalWritten := totalWritten + len;
    len := wr.WriteUInt32(hb.frameLength);
    totalWritten := totalWritten + len;
    reveal Msg.HeaderBodyToSeq();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(wr: Streams.ByteWriter, ha: Msg.HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID)
      returns (ret: Result<nat, string>)
    requires wr.Valid()
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret { case Success(_mcc#0) => (var totalWritten := _mcc#0; var serHa := ha.iv + ha.authenticationTag; var initLen := old(wr.GetSizeWritten()); initLen + totalWritten == wr.GetSizeWritten() && serHa == wr.GetDataWritten()[initLen .. initLen + totalWritten] && totalWritten == |serHa| && old(wr.GetDataWritten()) + serHa == wr.GetDataWritten()) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases wr, ha, algorithmSuiteID
  {
    var m := wr.WriteBytes(ha.iv);
    var n := wr.WriteBytes(ha.authenticationTag);
    return Success(m + n);
  }

  method SerializeAAD(wr: Streams.ByteWriter, kvPairs: EncryptionContext.Map) returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.Serializable(kvPairs)
    modifies wr.writer`data
    ensures wr.Valid() && EncryptionContext.Serializable(kvPairs)
    ensures match ret { case Success(_mcc#0) => (var totalWritten := _mcc#0; var serAAD := EncryptionContext.MapToLinear(kvPairs); var initLen := old(wr.GetSizeWritten()); totalWritten == |serAAD| && initLen + totalWritten == wr.GetSizeWritten() && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases wr, kvPairs
  {
    reveal EncryptionContext.Serializable();
    var totalWritten := 0;
    var kvPairsLength := EncryptionContext.ComputeLength(kvPairs);
    var len := wr.WriteUInt16(kvPairsLength as uint16);
    totalWritten := totalWritten + len;
    len :- SerializeKVPairs(wr, kvPairs);
    totalWritten := totalWritten + len;
    return Success(totalWritten);
  }

  method SerializeKVPairs(wr: Streams.ByteWriter, encryptionContext: EncryptionContext.Map) returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.SerializableKVPairs(encryptionContext)
    modifies wr.writer`data
    ensures wr.Valid() && EncryptionContext.SerializableKVPairs(encryptionContext)
    ensures match ret { case Success(_mcc#0) => (var newlyWritten := _mcc#0; var serAAD := EncryptionContext.MapToSeq(encryptionContext); newlyWritten == |serAAD| && wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten && wr.GetDataWritten() == old(wr.GetDataWritten()) + serAAD) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases wr, encryptionContext
  {
    var newlyWritten := 0;
    if |encryptionContext| == 0 {
      return Success(newlyWritten);
    }
    var len := wr.WriteUInt16(|encryptionContext| as uint16);
    newlyWritten := newlyWritten + len;
    var keys: seq<UTF8.ValidUTF8Bytes> := Sets.ComputeSetToOrderedSequence(encryptionContext.Keys, UInt.UInt8Less);
    ghost var kvPairs := seq(|keys|, (i: int) requires 0 <= i < |keys| => (keys[i], encryptionContext[keys[i]]));
    ghost var n := |keys|;
    ghost var writtenBeforeLoop := wr.GetDataWritten();
    assert writtenBeforeLoop == old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16);
    var j := 0;
    while j < |keys|
      invariant j <= n == |keys|
      invariant wr.GetDataWritten() == writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j)
      invariant wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten
      decreases |keys| - j
    {
      len :- SerializeKVPair(wr, keys[j], encryptionContext[keys[j]]);
      newlyWritten := newlyWritten + len;
      assert wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten;
      calc {
        wr.GetDataWritten();
      ==
        writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]);
      ==
        writtenBeforeLoop + (EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]));
      ==
        {
          assert EncryptionContext.LinearToSeq(kvPairs, 0, j) + EncryptionContext.KVPairToSeq(kvPairs[j]) == EncryptionContext.LinearToSeq(kvPairs, 0, j + 1);
        }
        writtenBeforeLoop + EncryptionContext.LinearToSeq(kvPairs, 0, j + 1);
      }
      j := j + 1;
    }
    return Success(newlyWritten);
  }

  method SerializeKVPair(wr: Streams.ByteWriter, k: UTF8.ValidUTF8Bytes, v: UTF8.ValidUTF8Bytes)
      returns (ret: Result<nat, string>)
    requires wr.Valid() && EncryptionContext.SerializableKVPair((k, v))
    modifies wr.writer`data
    ensures wr.Valid()
    ensures match ret { case Success(_mcc#0) => (var newlyWritten := _mcc#0; var serKV := EncryptionContext.KVPairToSeq((k, v)); newlyWritten == |serKV| && wr.GetSizeWritten() == old(wr.GetSizeWritten()) + newlyWritten && wr.GetDataWritten() == old(wr.GetDataWritten()) + serKV) case Failure(_mcc#1) => var e := _mcc#1; true }
    decreases wr, k, v
  {
    ghost var previouslyWritten := wr.GetDataWritten();
    var newlyWritten := 0;
    var len := wr.WriteUInt16(|k| as uint16);
    newlyWritten := newlyWritten + len;
    len := wr.WriteBytes(k);
    newlyWritten := newlyWritten + len;
    len := wr.WriteUInt16(|v| as uint16);
    newlyWritten := newlyWritten + len;
    len := wr.WriteBytes(v);
    newlyWritten := newlyWritten + len;
    calc {
      wr.GetDataWritten();
    ==
      previouslyWritten + UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v;
    ==
      previouslyWritten + (UInt16ToSeq(|k| as uint16) + k + UInt16ToSeq(|v| as uint16) + v);
    ==
      previouslyWritten + EncryptionContext.KVPairToSeq((k, v));
    }
    return Success(newlyWritten);
  }

  method SerializeEDKs(wr: Streams.ByteWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: nat)
    requires wr.Valid() && encryptedDataKeys.Valid()
    modifies wr.writer`data
    ensures wr.Valid() && encryptedDataKeys.Valid()
    ensures ret == |Msg.EDKsToSeq(encryptedDataKeys)|
    ensures old(wr.GetSizeWritten()) + ret == wr.GetSizeWritten()
    ensures wr.GetDataWritten() == old(wr.GetDataWritten()) + Msg.EDKsToSeq(encryptedDataKeys)
    decreases wr, encryptedDataKeys
  {
    var totalWritten := 0;
    var len := wr.WriteUInt16(|encryptedDataKeys.entries| as uint16);
    totalWritten := totalWritten + len;
    var j := 0;
    ghost var n := |encryptedDataKeys.entries|;
    while j < |encryptedDataKeys.entries|
      invariant j <= n == |encryptedDataKeys.entries|
      invariant wr.GetDataWritten() == old(wr.GetDataWritten()) + UInt16ToSeq(n as uint16) + Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j)
      invariant totalWritten == 2 + |Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j)|
      decreases |encryptedDataKeys.entries| - j
    {
      var entry := encryptedDataKeys.entries[j];
      len := wr.WriteUInt16(|entry.keyProviderId| as uint16);
      totalWritten := totalWritten + len;
      len := wr.WriteBytes(entry.keyProviderId);
      totalWritten := totalWritten + len;
      len := wr.WriteUInt16(|entry.keyProviderInfo| as uint16);
      totalWritten := totalWritten + len;
      len := wr.WriteBytes(entry.keyProviderInfo);
      totalWritten := totalWritten + len;
      len := wr.WriteUInt16(|entry.ciphertext| as uint16);
      totalWritten := totalWritten + len;
      len := wr.WriteBytes(entry.ciphertext);
      totalWritten := totalWritten + len;
      j := j + 1;
    }
    return totalWritten;
  }
}

module Actions {

  import opened Wrappers = Wrappers
  trait {:termination false} Action<A, R> {
    method Invoke(a: A) returns (r: R)
      ensures Ensures(a, r)

    predicate Ensures(a: A, r: R)
  }

  trait {:termination false} ActionWithResult<A, R, E> extends Action<A, Result<R, E>> {
    method Invoke(a: A) returns (res: Result<R, E>)
      ensures Ensures(a, res)
  }

  method Map<A, R>(action: Action<A, R>, s: seq<A>) returns (res: seq<R>)
    ensures |s| == |res|
    ensures forall i: int :: true && 0 <= i < |s| ==> action.Ensures(s[i], res[i])
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], rs[j])
    {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  method MapWithResult<A, R(0), E>(action: ActionWithResult<A, R, E>, s: seq<A>) returns (res: Result<seq<R>, E>)
    ensures res.Success? ==> |s| == |res.value|
    ensures res.Success? ==> forall i: int :: true && 0 <= i < |s| ==> action.Ensures(s[i], Success(res.value[i]))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], Success(rs[j]))
    {
      var r :- action.Invoke(s[i]);
      rs := rs + [r];
    }
    return Success(rs);
  }

  method Filter<A>(action: Action<A, bool>, s: seq<A>) returns (res: seq<A>)
    ensures |s| >= |res|
    ensures forall j: A :: j in res ==> j in s && action.Ensures(j, true)
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A :: j in rs ==> j in s && action.Ensures(j, true)
    {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }

  method FilterWithResult<A, E>(action: ActionWithResult<A, bool, E>, s: seq<A>) returns (res: Result<seq<A>, E>)
    ensures res.Success? ==> |s| >= |res.value| && forall j: A :: j in res.value ==> j in s && action.Ensures(j, Success(true))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A :: j in rs ==> j in s && action.Ensures(j, Success(true))
    {
      var r :- action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  method ReduceToSuccess<A, B, E>(action: ActionWithResult<A, B, E>, s: seq<A>) returns (res: Result<B, seq<E>>)
    ensures res.Success? ==> exists a: A | a in s :: action.Ensures(a, Success(res.value))
    decreases action, s
  {
    var errors := [];
    for i: int := 0 to |s| {
      var attempt := action.Invoke(s[i]);
      if attempt.Success? {
        return Success(attempt.value);
      } else {
        errors := errors + [attempt.error];
      }
    }
    return Failure(errors);
  }
}

module Base64 {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  newtype index = x: int
    | 0 <= x < 64

  newtype uint24 = x: int
    | 0 <= x < 16777216

  predicate method IsBase64Char(c: char)
    decreases c
  {
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  predicate method IsUnpaddedBase64String(s: string)
    decreases s
  {
    |s| % 4 == 0 &&
    forall k: char :: 
      k in s ==>
        IsBase64Char(k)
  }

  function method IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
    decreases i
  {
    if i == 63 then
      '/'
    else if i == 62 then
      '+'
    else if 52 <= i <= 61 then
      (i - 4) as char
    else if 26 <= i <= 51 then
      i as char + 71 as char
    else
      i as char + 65 as char
  }

  function method CharToIndex(c: char): (i: index)
    requires IsBase64Char(c)
    ensures IndexToChar(i) == c
    decreases c
  {
    if c == '/' then
      63
    else if c == '+' then
      62
    else if '0' <= c <= '9' then
      (c + 4 as char) as index
    else if 'a' <= c <= 'z' then
      (c - 71 as char) as index
    else
      (c - 65 as char) as index
  }

  lemma CharToIndexToChar(x: char)
    requires IsBase64Char(x)
    ensures IndexToChar(CharToIndex(x)) == x
    decreases x
  {
  }

  lemma IndexToCharToIndex(x: index)
    ensures CharToIndex(IndexToChar(x)) == x
    decreases x
  {
  }

  function method UInt24ToSeq(x: uint24): (ret: seq<uint8>)
    ensures |ret| == 3
    ensures ret[0] as uint24 * 65536 + ret[1] as uint24 * 256 + ret[2] as uint24 == x
    decreases x
  {
    var b0: uint8 := (x / 65536) as uint8;
    var x0: uint24 := x - b0 as uint24 * 65536;
    var b1: uint8 := (x0 / 256) as uint8;
    var b2: uint8 := (x0 % 256) as uint8;
    [b0, b1, b2]
  }

  function method SeqToUInt24(s: seq<uint8>): (x: uint24)
    requires |s| == 3
    ensures UInt24ToSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 65536 + s[1] as uint24 * 256 + s[2] as uint24
  }

  lemma UInt24ToSeqToUInt24(x: uint24)
    ensures SeqToUInt24(UInt24ToSeq(x)) == x
    decreases x
  {
  }

  lemma SeqToUInt24ToSeq(s: seq<uint8>)
    requires |s| == 3
    ensures UInt24ToSeq(SeqToUInt24(s)) == s
    decreases s
  {
  }

  function method UInt24ToIndexSeq(x: uint24): (ret: seq<index>)
    ensures |ret| == 4
    ensures ret[0] as uint24 * 262144 + ret[1] as uint24 * 4096 + ret[2] as uint24 * 64 + ret[3] as uint24 == x
    decreases x
  {
    var b0: index := (x / 262144) as index;
    var x0: uint24 := x - b0 as uint24 * 262144;
    var b1: index := (x0 / 4096) as index;
    var x1: uint24 := x0 - b1 as uint24 * 4096;
    var b2: index := (x1 / 64) as index;
    var b3: index := (x1 % 64) as index;
    [b0, b1, b2, b3]
  }

  function method IndexSeqToUInt24(s: seq<index>): (x: uint24)
    requires |s| == 4
    ensures UInt24ToIndexSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 262144 + s[1] as uint24 * 4096 + s[2] as uint24 * 64 + s[3] as uint24
  }

  lemma UInt24ToIndexSeqToUInt24(x: uint24)
    ensures IndexSeqToUInt24(UInt24ToIndexSeq(x)) == x
    decreases x
  {
  }

  lemma IndexSeqToUInt24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures UInt24ToIndexSeq(IndexSeqToUInt24(s)) == s
    decreases s
  {
  }

  function method DecodeBlock(s: seq<index>): (ret: seq<uint8>)
    requires |s| == 4
    ensures |ret| == 3
    ensures UInt24ToIndexSeq(SeqToUInt24(ret)) == s
    decreases s
  {
    UInt24ToSeq(IndexSeqToUInt24(s))
  }

  function method EncodeBlock(s: seq<uint8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
    ensures UInt24ToSeq(IndexSeqToUInt24(ret)) == s
    ensures DecodeBlock(ret) == s
    decreases s
  {
    UInt24ToIndexSeq(SeqToUInt24(s))
  }

  lemma EncodeDecodeBlock(s: seq<uint8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
    decreases s
  {
  }

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
    decreases s
  {
  }

  function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
    requires |s| % 4 == 0
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    ensures |b| == 0 ==> |s| == 0
    ensures |b| != 0 ==> EncodeBlock(b[..3]) == s[..4]
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  }

  function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
    ensures DecodeRecursively(s) == b
    decreases b
  {
    if |b| == 0 then
      []
    else
      EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  }

  lemma /*{:_induction s}*/ DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures EncodeRecursively(DecodeRecursively(s)) == s
    decreases s
  {
  }

  lemma /*{:_induction b}*/ EncodeDecodeRecursively(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeRecursively(EncodeRecursively(b)) == b
    decreases b
  {
  }

  function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k: char :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
    ensures forall k: int :: 0 <= k < |b| ==> IndexToChar(b[k]) == s[k]
    decreases s
  {
    seq(|s|, (i: int) requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k: char :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
    ensures forall k: int :: 0 <= k < |s| ==> CharToIndex(s[k]) == b[k]
    ensures FromCharsToIndices(s) == b
    decreases b
  {
    seq(|b|, (i: int) requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k: char :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
    decreases s
  {
  }

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
    decreases b
  {
  }

  function method DecodeUnpadded(s: seq<char>): (b: seq<uint8>)
    requires IsUnpaddedBase64String(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    decreases s
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method EncodeUnpadded(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeUnpadded(s) == b
    decreases b
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeDecodeUnpadded(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeUnpadded(EncodeUnpadded(b)) == b
    decreases b
  {
  }

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedBase64String(s)
    ensures EncodeUnpadded(DecodeUnpadded(s)) == s
    decreases s
  {
    ghost var fromCharsToIndicesS := FromCharsToIndices(s);
    calc {
      EncodeUnpadded(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeRecursively(FromCharsToIndices(s)));
    ==
      EncodeUnpadded(DecodeRecursively(fromCharsToIndicesS));
    ==
      assert |fromCharsToIndicesS| % 4 == 0; assert |DecodeRecursively(fromCharsToIndicesS)| % 3 == 0; FromIndicesToChars(EncodeRecursively(DecodeRecursively(fromCharsToIndicesS)));
    ==
      {
        DecodeEncodeRecursively(fromCharsToIndicesS);
      }
      FromIndicesToChars(fromCharsToIndicesS);
    ==
      FromIndicesToChars(FromCharsToIndices(s));
    ==
      {
        FromCharsToIndicesToChars(s);
      }
      s;
    }
  }

  predicate method Is1Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    CharToIndex(s[2]) % 4 == 0 &&
    s[3] == '='
  }

  function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
    requires Is1Padding(s)
    ensures |b| == 2
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  function method Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], b[1], 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']
  }

  lemma DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode1Padding(b: seq<uint8>)
    requires |b| == 2
    ensures Decode1Padding(Encode1Padding(b)) == b
    decreases b
  {
  }

  predicate method Is2Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    CharToIndex(s[1]) % 16 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
    requires Is2Padding(s)
    ensures |b| == 1
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], 0, 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']
  }

  lemma DecodeEncode2Padding(s: seq<char>)
    requires Is2Padding(s)
    ensures Encode2Padding(Decode2Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode2Padding(b: seq<uint8>)
    requires |b| == 1
    ensures Decode2Padding(Encode2Padding(b)) == b
    decreases b
  {
  }

  predicate method IsBase64String(s: string)
    decreases s
  {
    var finalBlockStart: int := |s| - 4;
    |s| % 4 == 0 &&
    (IsUnpaddedBase64String(s) || (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
    decreases s
  {
    if s == [] then
      []
    else
      var finalBlockStart: int := |s| - 4; var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; if Is1Padding(suffix) then DecodeUnpadded(prefix) + Decode1Padding(suffix) else if Is2Padding(suffix) then DecodeUnpadded(prefix) + Decode2Padding(suffix) else DecodeUnpadded(s)
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<uint8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> ghost var finalBlockStart: int := |s| - 4; ghost var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; (Is1Padding(suffix) ==> |b| % 3 == 2) && (Is2Padding(suffix) ==> |b| % 3 == 1) && (!Is1Padding(suffix) && !Is2Padding(suffix) ==> |b| % 3 == 0)
    decreases s, b
  {
    if 4 <= |s| {
      ghost var finalBlockStart := |s| - 4;
      ghost var prefix, suffix := s[..finalBlockStart], s[finalBlockStart..];
      if s == [] {
      } else if Is1Padding(suffix) {
        assert !Is2Padding(suffix);
        ghost var x, y := DecodeUnpadded(prefix), Decode1Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 2;
        Mod3(|x| / 3, |y|, |b|);
      } else if Is2Padding(suffix) {
        ghost var x, y := DecodeUnpadded(prefix), Decode2Padding(suffix);
        assert b == x + y;
        assert |x| == |x| / 3 * 3 && |y| == 1;
        Mod3(|x| / 3, |y|, |b|);
      } else {
        assert b == DecodeUnpadded(s);
      }
    }
  }

  lemma Mod3(x: nat, k: nat, n: nat)
    requires 0 <= k < 3 && n == 3 * x + k
    ensures n % 3 == k
    decreases x, k, n
  {
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>, string>)
    ensures IsBase64String(s) ==> b.Success?
    ensures !IsBase64String(s) ==> b.Failure?
    decreases s
  {
    if IsBase64String(s) then
      Success(DecodeValid(s))
    else
      Failure(""The encoding is malformed"")
  }

  predicate StringIs7Bit(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] < 128 as char
  }

  function method Encode(b: seq<uint8>): (s: seq<char>)
    ensures StringIs7Bit(s)
    ensures |s| % 4 == 0
    ensures IsBase64String(s)
    decreases b
  {
    if |b| % 3 == 0 then
      EncodeUnpadded(b)
    else if |b| % 3 == 1 then
      EncodeUnpadded(b[..|b| - 1]) + Encode2Padding(b[|b| - 1..])
    else
      EncodeUnpadded(b[..|b| - 2]) + Encode1Padding(b[|b| - 2..])
  }

  lemma EncodeLengthExact(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); (|b| % 3 == 0 ==> |s| == |b| / 3 * 4) && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
    decreases b
  {
    ghost var s := Encode(b);
    if |b| % 3 == 0 {
      assert s == EncodeUnpadded(b);
      assert |s| == |b| / 3 * 4;
    } else if |b| % 3 == 1 {
      assert s == EncodeUnpadded(b[..|b| - 1]) + Encode2Padding(b[|b| - 1..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..|b| - 1])| + |Encode2Padding(b[|b| - 1..])|;
      ==
        {
          assert |Encode2Padding(b[|b| - 1..])| == 4;
        }
        |EncodeUnpadded(b[..|b| - 1])| + 4;
      ==
        {
          assert |EncodeUnpadded(b[..|b| - 1])| == |b[..|b| - 1]| / 3 * 4;
        }
        |b[..|b| - 1]| / 3 * 4 + 4;
      ==
        {
          assert |b[..|b| - 1]| == |b| - 1;
        }
        (|b| - 1) / 3 * 4 + 4;
      ==
        {
          assert (|b| - 1) / 3 == |b| / 3;
        }
        |b| / 3 * 4 + 4;
      }
    } else {
      assert s == EncodeUnpadded(b[..|b| - 2]) + Encode1Padding(b[|b| - 2..]);
      calc {
        |s|;
      ==
        |EncodeUnpadded(b[..|b| - 2])| + |Encode1Padding(b[|b| - 2..])|;
      ==
        {
          assert |Encode1Padding(b[|b| - 2..])| == 4;
        }
        |EncodeUnpadded(b[..|b| - 2])| + 4;
      ==
        {
          assert |EncodeUnpadded(b[..|b| - 2])| == |b[..|b| - 2]| / 3 * 4;
        }
        |b[..|b| - 2]| / 3 * 4 + 4;
      ==
        {
          assert |b[..|b| - 2]| == |b| - 2;
        }
        (|b| - 2) / 3 * 4 + 4;
      ==
        {
          assert (|b| - 2) / 3 == |b| / 3;
        }
        |b| / 3 * 4 + 4;
      }
      assert ghost var s: seq<char> := Encode(b); (|b| % 3 == 0 ==> |s| == |b| / 3 * 4) && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4);
    }
  }

  lemma EncodeLengthBound(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); |s| <= |b| / 3 * 4 + 4
    decreases b
  {
    EncodeLengthExact(b);
  }
}

module Base64Lemmas {

  import opened StandardLibrary = StandardLibrary

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened Base64 = Base64
  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[|s| - 4..])
    requires !Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      Encode(DecodeUnpadded(s));
    ==
      EncodeUnpadded(DecodeUnpadded(s));
    ==
      {
        DecodeEncodeUnpadded(s);
      }
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 2] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 2..] == Decode1Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 2; EncodeUnpadded(DecodeValid(s)[..|DecodeValid(s)| - 2]) + Encode1Padding(DecodeValid(s)[|DecodeValid(s)| - 2..]);
    ==
      {
        DecodeValidUnpaddedPartialFrom1PaddedSeq(s);
      }
      EncodeUnpadded(DecodeUnpadded(s[..|s| - 4])) + Encode1Padding(DecodeValid(s)[|DecodeValid(s)| - 2..]);
    ==
      {
        DecodeEncodeUnpadded(s[..|s| - 4]);
      }
      s[..|s| - 4] + Encode1Padding(DecodeValid(s)[|DecodeValid(s)| - 2..]);
    ==
      {
        DecodeValid1PaddedPartialFrom1PaddedSeq(s);
      }
      s[..|s| - 4] + Encode1Padding(Decode1Padding(s[|s| - 4..]));
    ==
      {
        DecodeEncode1Padding(s[|s| - 4..]);
      }
      s[..|s| - 4] + s[|s| - 4..];
    ==
      {
        SeqPartsMakeWhole(s, |s| - 4);
      }
      s;
    }
  }

  lemma DecodeValidUnpaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 1] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid2PaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 1..] == Decode2Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
    calc {
      Encode(DecodeValid(s));
    ==
      assert |DecodeValid(s)| % 3 == 1; EncodeUnpadded(DecodeValid(s)[..|DecodeValid(s)| - 1]) + Encode2Padding(DecodeValid(s)[|DecodeValid(s)| - 1..]);
    ==
      {
        DecodeValidUnpaddedPartialFrom2PaddedSeq(s);
      }
      EncodeUnpadded(DecodeUnpadded(s[..|s| - 4])) + Encode2Padding(DecodeValid(s)[|DecodeValid(s)| - 1..]);
    ==
      {
        DecodeEncodeUnpadded(s[..|s| - 4]);
      }
      s[..|s| - 4] + Encode2Padding(DecodeValid(s)[|DecodeValid(s)| - 1..]);
    ==
      {
        DecodeValid2PaddedPartialFrom2PaddedSeq(s);
      }
      s[..|s| - 4] + Encode2Padding(Decode2Padding(s[|s| - 4..]));
    ==
      {
        DecodeEncode2Padding(s[|s| - 4..]);
      }
      s[..|s| - 4] + s[|s| - 4..];
    ==
      {
        SeqPartsMakeWhole(s, |s| - 4);
      }
      s;
    }
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
    if s == [] {
      calc {
        Encode(DecodeValid(s));
      ==
        {
          DecodeValidEncodeEmpty(s);
        }
        s;
      }
    } else if |s| >= 4 && Is1Padding(s[|s| - 4..]) {
      calc {
        Encode(DecodeValid(s));
      ==
        {
          DecodeValidEncode1Padding(s);
        }
        s;
      }
    } else if |s| >= 4 && Is2Padding(s[|s| - 4..]) {
      calc {
        Encode(DecodeValid(s));
      ==
        {
          DecodeValidEncode2Padding(s);
        }
        s;
      }
    } else {
      calc {
        Encode(DecodeValid(s));
      ==
        {
          DecodeValidEncodeUnpadded(s);
        }
        s;
      }
    }
  }

  lemma EncodeDecodeValid(b: seq<uint8>)
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
    decreases s
  {
    calc {
      Encode(Decode(s).value);
    ==
      {
        DecodeValidEncode(s);
      }
      s;
    }
  }

  lemma EncodeDecode(b: seq<uint8>)
    ensures Decode(Encode(b)) == Success(b)
    decreases b
  {
    calc {
      Decode(Encode(b));
    ==
      {
        assert IsBase64String(Encode(b));
      }
      Success(DecodeValid(Encode(b)));
    ==
      {
        EncodeDecodeValid(b);
      }
      Success(b);
    }
  }
}

module StandardLibrary {

  import opened Wrappers = Wrappers

  import opened U = UInt
  function method {:tailrecursion} Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method {:tailrecursion} Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    if i.Some? then
      [s[..i.value]] + Split(s[i.value + 1..], delim)
    else
      [s]
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i: int :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
    decreases s, prefix
  {
    calc {
      Split(s, delim);
    ==
      ghost var i: Option<nat> := FindIndexMatching(s, delim, 0); if i.Some? then [s[..i.value]] + Split(s[i.value + 1..], delim) else [s];
    ==
      {
        FindIndexMatchingLocatesElem(s, delim, 0, |prefix|);
        assert FindIndexMatching(s, delim, 0).Some?;
      }
      [s[..|prefix|]] + Split(s[|prefix| + 1..], delim);
    ==
      {
        assert s[..|prefix|] == prefix;
      }
      [prefix] + Split(s[|prefix| + 1..], delim);
    }
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
    calc {
      Split(s, delim);
    ==
      ghost var i: Option<nat> := FindIndexMatching(s, delim, 0); if i.Some? then [s[..i.value]] + Split(s[i.value + 1..], delim) else [s];
    ==
      {
        FindIndexMatchingLocatesElem(s, delim, 0, |s|);
      }
      [s];
    }
  }

  lemma FindIndexMatchingLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i: int :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures FindIndexMatching(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
  {
  }

  function method FindIndexMatching<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && s[index.value] == c && c !in s[i .. index.value]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    FindIndex(s, (x: T) => x == c, i)
  }

  function method {:tailrecursion} FindIndex<T>(s: seq<T>, f: T -> bool, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && f(s[index.value]) && forall j: int :: i <= j < index.value ==> !f(s[j])
    ensures index.None? ==> forall j: int :: i <= j < |s| ==> !f(s[j])
    decreases |s| - i
  {
    if i == |s| then
      None
    else if f(s[i]) then
      Some(i)
    else
      FindIndex(s, f, i + 1)
  }

  function method {:tailrecursion} Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
    if s == [] {
      assert s + s' == s';
    } else {
      ghost var S := s + s';
      ghost var s1 := s[1..];
      calc {
        Filter(S, f);
      ==
        if f(S[0]) then [S[0]] + Filter(S[1..], f) else Filter(S[1..], f);
      ==
        {
          assert S[0] == s[0] && S[1..] == s1 + s';
        }
        if f(s[0]) then [s[0]] + Filter(s1 + s', f) else Filter(s1 + s', f);
      ==
        {
          FilterIsDistributive(s1, s', f);
        }
        if f(s[0]) then [s[0]] + (Filter(s1, f) + Filter(s', f)) else Filter(s1, f) + Filter(s', f);
      ==
        if f(s[0]) then [s[0]] + Filter(s1, f) + Filter(s', f) else Filter(s1, f) + Filter(s', f);
      ==
        (if f(s[0]) then [s[0]] + Filter(s1, f) else Filter(s1, f)) + Filter(s', f);
      ==
        Filter(s, f) + Filter(s', f);
      }
    }
  }

  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
    decreases s, i
  {
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    (forall x: T, y: T :: 
      less(x, y) || x == y || less(y, x)) &&
    (forall x: T, y: T :: 
      less(x, y) &&
      less(y, x) ==>
        false) &&
    forall x: T, y: T :: 
      less(x, y) ==>
        x != y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LexicographicLessOrEqual(a, a, less)
    decreases a
  {
    assert LexicographicLessOrEqualAux(a, a, less, |a|);
  }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, a, less)
    ensures a == b
    decreases a, b
  {
    assert LessIrreflexive: forall x: T, y: T :: less(x, y) ==> x != y by {
      reveal Trich;
    }
    assert ASymmetric: forall x: T, y: T :: less(x, y) && less(y, x) ==> false by {
      reveal Trich;
    }
    ghost var k0 :| 0 <= k0 <= |a| && LexicographicLessOrEqualAux(a, b, less, k0);
    ghost var k1 :| 0 <= k1 <= |b| && LexicographicLessOrEqualAux(b, a, less, k1);
    ghost var max := if k0 < k1 then k1 else k0;
    assert max <= |a| && max <= |b|;
    assert SameUntilMax: forall i: int :: 0 <= i < max ==> a[i] == b[i];
    assert AA: k0 == |a| || (k0 < |b| && less(a[k0], b[k0]));
    assert BB: k1 == |b| || (k1 < |a| && less(b[k1], a[k1]));
    calc {
      true;
    ==>
      {
        reveal AA, BB;
      }
      (k0 == |a| || (k0 < |b| && less(a[k0], b[k0]))) &&
      (k1 == |b| || (k1 < |a| && less(b[k1], a[k1])));
    ==
      (k0 == |a| && k1 == |b|) || (k0 == |a| && k1 < |a| && less(b[k1], a[k1])) || (k0 < |b| && less(a[k0], b[k0]) && k1 == |b|) || (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]));
    ==
      {
        reveal LessIrreflexive, SameUntilMax;
      }
      (k0 == |a| && k1 == |b|) || (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]));
    ==>
      {
        reveal LessIrreflexive, SameUntilMax;
        assert max <= k0 && max <= k1;
      }
      (k0 == |a| && k1 == |b|) || (k0 < |b| && less(a[k0], b[k0]) && k1 < |a| && less(b[k1], a[k1]) && k0 == k1 == max);
    ==
      {
        reveal ASymmetric;
      }
      k0 == |a| &&
      k1 == |b|;
    ==>
      {
        assert |a| == k0 <= max && |b| == k1 <= max ==> k0 == k1;
      }
      max == |a| == |b|;
    ==>
      {
        reveal SameUntilMax;
      }
      a == b;
    }
  }

  lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, c, less)
    ensures LexicographicLessOrEqual(a, c, less)
    decreases a, b, c
  {
    ghost var k0 :| 0 <= k0 <= |a| && LexicographicLessOrEqualAux(a, b, less, k0);
    ghost var k1 :| 0 <= k1 <= |b| && LexicographicLessOrEqualAux(b, c, less, k1);
    ghost var k := if k0 < k1 then k0 else k1;
    assert LexicographicLessOrEqualAux(a, c, less, k);
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
    ghost var m := 0;
    while m < |a| && m < |b| && a[m] == b[m]
      invariant m <= |a| && m <= |b|
      invariant forall i: int :: 0 <= i < m ==> a[i] == b[i]
      decreases |a| - m, if m < |a| then |b| - m else 0 - 1
    {
      m := m + 1;
    }
    if m == |a| == |b| {
      assert a == b;
      LexIsReflexive(a, less);
    } else if m == |a| < |b| {
      assert LexicographicLessOrEqualAux(a, b, less, m);
    } else if m == |b| < |a| {
      assert LexicographicLessOrEqualAux(b, a, less, m);
    } else {
      assert m < |a| && m < |b|;
      reveal Trich;
      if
      case less(a[m], b[m]) =>
        assert LexicographicLessOrEqualAux(a, b, less, m);
      case less(b[m], a[m]) =>
        assert LexicographicLessOrEqualAux(b, a, less, m);
    }
  }

  function method {:tailrecursion} SetToOrderedSequence<T(==,!new)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i: int :: 0 <= i < |q| ==> q[i] in s
    ensures forall k: seq<T> :: k in s ==> k in q
    ensures forall i: int :: 0 < i < |q| ==> LexicographicLessOrEqual(q[i - 1], q[i], less)
    ensures forall i: int, j: int | 0 <= i < j < |q| :: q[i] != q[j]
    decreases s
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s, less); assert forall a: seq<T>, b: seq<T> :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
    forall a: seq<T>, b: seq<T> | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
      MinimumIsUnique(a, b, s, less);
    }
  } var a: seq<T> :| a in s && IsMinimum(a, s, less); [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    decreases a, s
  {
    a in s &&
    forall z: seq<T> :: 
      z in s ==>
        LexicographicLessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a: seq<T> :: IsMinimum(a, s, less)
    decreases s
  {
    ghost var a := FindMinimum(s, less);
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
    decreases a, b, s
  {
    LexIsAntisymmetric(a, b, less);
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
    decreases s
  {
    a :| a in s;
    if s == {a} {
      LexIsReflexive(a, less);
    } else {
      ghost var s' := s - {a};
      assert forall x: seq<T> :: x in s <==> x == a || x in s';
      ghost var a' := FindMinimum(s', less);
      if LexicographicLessOrEqual(a', a, less) {
        a := a';
      } else {
        assert LexicographicLessOrEqual(a, a', less) by {
          LexIsTotal(a, a', less);
        }
        forall z: seq<T> | z in s
          ensures LexicographicLessOrEqual(a, z, less)
        {
          if z == a {
            LexIsReflexive(a, less);
          } else {
            calc {
              true;
            ==
              z in s';
            ==>
              LexicographicLessOrEqual(a', z, less);
            ==>
              {
                LexIsTransitive(a, a', z, less);
              }
              LexicographicLessOrEqual(a, z, less);
            }
          }
        }
      }
    }
  }

  module UInt {
    newtype uint8 = x: int
      | 0 <= x < 256

    newtype uint16 = x: int
      | 0 <= x < 65536

    newtype uint32 = x: int
      | 0 <= x < 4294967296

    newtype uint64 = x: int
      | 0 <= x < 18446744073709551616

    newtype int32 = x: int
      | -2147483648 <= x < 2147483648

    newtype int64 = x: int
      | -9223372036854775808 <= x < 9223372036854775808

    const UINT16_LIMIT := 65536
    const UINT32_LIMIT := 4294967296
    const INT32_MAX_LIMIT := 2147483648
    const INT64_MAX_LIMIT := 9223372036854775808

    predicate method UInt8Less(a: uint8, b: uint8)
      decreases a, b
    {
      a < b
    }

    function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
      ensures |ret| == 2
      ensures 256 * ret[0] as uint16 + ret[1] as uint16 == x
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): (x: uint16)
      requires |s| == 2
      ensures UInt16ToSeq(x) == s
      decreases s
    {
      var x0: uint16 := s[0] as uint16 * 256;
      x0 + s[1] as uint16
    }

    lemma UInt16SeqSerializeDeserialize(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
      ensures |ret| == 4
      ensures 16777216 * ret[0] as uint32 + 65536 * ret[1] as uint32 + 256 * ret[2] as uint32 + ret[3] as uint32 == x
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): (x: uint32)
      requires |s| == 4
      ensures UInt32ToSeq(x) == s
      decreases s
    {
      var x0: uint32 := s[0] as uint32 * 16777216;
      var x1: uint32 := x0 + s[1] as uint32 * 65536;
      var x2: uint32 := x1 + s[2] as uint32 * 256;
      x2 + s[3] as uint32
    }

    lemma UInt32SeqSerializeDeserialize(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
      ensures |ret| == 8
      ensures 72057594037927936 * ret[0] as uint64 + 281474976710656 * ret[1] as uint64 + 1099511627776 * ret[2] as uint64 + 4294967296 * ret[3] as uint64 + 16777216 * ret[4] as uint64 + 65536 * ret[5] as uint64 + 256 * ret[6] as uint64 + ret[7] as uint64 == x
      decreases x
    {
      var b0: uint8 := (x / 72057594037927936) as uint8;
      var x0: uint64 := x - b0 as uint64 * 72057594037927936;
      var b1: uint8 := (x0 / 281474976710656) as uint8;
      var x1: uint64 := x0 - b1 as uint64 * 281474976710656;
      var b2: uint8 := (x1 / 1099511627776) as uint8;
      var x2: uint64 := x1 - b2 as uint64 * 1099511627776;
      var b3: uint8 := (x2 / 4294967296) as uint8;
      var x3: uint64 := x2 - b3 as uint64 * 4294967296;
      var b4: uint8 := (x3 / 16777216) as uint8;
      var x4: uint64 := x3 - b4 as uint64 * 16777216;
      var b5: uint8 := (x4 / 65536) as uint8;
      var x5: uint64 := x4 - b5 as uint64 * 65536;
      var b6: uint8 := (x5 / 256) as uint8;
      var b7: uint8 := (x5 % 256) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method SeqToUInt64(s: seq<uint8>): (x: uint64)
      requires |s| == 8
      ensures UInt64ToSeq(x) == s
      decreases s
    {
      var x0: uint64 := s[0] as uint64 * 72057594037927936;
      var x1: uint64 := x0 + s[1] as uint64 * 281474976710656;
      var x2: uint64 := x1 + s[2] as uint64 * 1099511627776;
      var x3: uint64 := x2 + s[3] as uint64 * 4294967296;
      var x4: uint64 := x3 + s[4] as uint64 * 16777216;
      var x5: uint64 := x4 + s[5] as uint64 * 65536;
      var x6: uint64 := x5 + s[6] as uint64 * 256;
      var x: uint64 := x6 + s[7] as uint64;
      UInt64SeqSerialize(x, s);
      x
    }

    lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
      requires |s| == 8
      requires 72057594037927936 * s[0] as uint64 + 281474976710656 * s[1] as uint64 + 1099511627776 * s[2] as uint64 + 4294967296 * s[3] as uint64 + 16777216 * s[4] as uint64 + 65536 * s[5] as uint64 + 256 * s[6] as uint64 + s[7] as uint64 == x
      ensures UInt64ToSeq(x) == s
      decreases x, s
    {
      calc {
        UInt64ToSeq(x);
      ==
        UInt64ToSeq(s[0] as uint64 * 72057594037927936 + s[1] as uint64 * 281474976710656 + s[2] as uint64 * 1099511627776 + s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64);
      ==
        ghost var b0: uint8 := ((s[0] as uint64 * 72057594037927936 + s[1] as uint64 * 281474976710656 + s[2] as uint64 * 1099511627776 + s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64) / 72057594037927936) as uint8; assert b0 == s[0]; ghost var x0: uint64 := s[0] as uint64 * 72057594037927936 + s[1] as uint64 * 281474976710656 + s[2] as uint64 * 1099511627776 + s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64 - b0 as uint64 * 72057594037927936; assert x0 == s[1] as uint64 * 281474976710656 + s[2] as uint64 * 1099511627776 + s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64; ghost var b1: uint8 := (x0 / 281474976710656) as uint8; assert b1 == s[1]; ghost var x1: uint64 := x0 - b1 as uint64 * 281474976710656; assert x1 == s[2] as uint64 * 1099511627776 + s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64; ghost var b2: uint8 := (x1 / 1099511627776) as uint8; assert b2 == s[2]; ghost var x2: uint64 := x1 - b2 as uint64 * 1099511627776; assert x2 == s[3] as uint64 * 4294967296 + s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64; ghost var b3: uint8 := (x2 / 4294967296) as uint8; assert b3 == s[3]; ghost var x3: uint64 := x2 - b3 as uint64 * 4294967296; assert x3 == s[4] as uint64 * 16777216 + s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64; ghost var b4: uint8 := (x3 / 16777216) as uint8; assert b4 == s[4]; ghost var x4: uint64 := x3 - b4 as uint64 * 16777216; assert x4 == s[5] as uint64 * 65536 + s[6] as uint64 * 256 + s[7] as uint64; ghost var b5: uint8 := (x4 / 65536) as uint8; assert b5 == s[5]; ghost var x5: uint64 := x4 - b5 as uint64 * 65536; assert x5 == s[6] as uint64 * 256 + s[7] as uint64; ghost var b6: uint8 := (x5 / 256) as uint8; assert b6 == s[6]; ghost var b7: uint8 := (x5 % 256) as uint8; assert b7 == s[7]; [b0, b1, b2, b3, b4, b5, b6, b7];
      ==
        [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]];
      ==
        s;
      }
    }

    lemma UInt64SeqSerializeDeserialize(x: uint64)
      ensures SeqToUInt64(UInt64ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 8
      ensures UInt64ToSeq(SeqToUInt64(s)) == s
      decreases s
    {
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        ghost var finalIndex: int := |s| - 1; SeqToNat(s[..finalIndex]) * 256 + s[finalIndex] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
      if s == [] {
      } else {
        ghost var s' := [0] + s;
        ghost var sLength := |s|;
        ghost var sFinalIndex := sLength - 1;
        calc {
          SeqToNat(s);
        ==
          SeqToNat(s[..sFinalIndex]) * 256 + s[sFinalIndex] as nat;
        ==
          SeqToNat([0] + s[..sFinalIndex]) * 256 + s[sFinalIndex] as nat;
        ==
          {
            assert s'[..sLength] == [0] + s[..sFinalIndex] && s'[sLength] == s[sFinalIndex];
          }
          SeqToNat(s'[..sLength]) * 256 + s'[sLength] as nat;
        ==
          SeqToNat(s');
        ==
          SeqToNat([0] + s);
        }
      }
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires ghost var suffixStartIndex: int := |s| - 4; s[suffixStartIndex..] == UInt32ToSeq(n as uint32) && forall i: int :: 0 <= i < suffixStartIndex ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
      if |s| == 4 {
        calc {
          SeqToNat(s);
        ==
          SeqToNat(s[..3]) * 256 + s[3] as nat;
        ==
          {
            assert s[..3][..2] == s[..2] && s[..3][2] == s[2];
          }
          (SeqToNat(s[..2]) * 256 + s[2] as nat) * 256 + s[3] as nat;
        ==
          {
            assert s[..2][..1] == s[..1] && s[..2][1] == s[1];
          }
          ((SeqToNat(s[..1]) * 256 + s[1] as nat) * 256 + s[2] as nat) * 256 + s[3] as nat;
        ==
          {
            assert s[..1][..0] == s[..0] && s[..1][0] == s[0];
          }
          (((SeqToNat(s[..0]) * 256 + s[0] as nat) * 256 + s[1] as nat) * 256 + s[2] as nat) * 256 + s[3] as nat;
        ==
          n;
        }
      } else {
        assert s == [0] + s[1..];
        SeqToNatZeroPrefix(s[1..]);
        SeqWithUInt32Suffix(s[1..], n);
      }
    }
  }
}

module {:extern ""Sets""} Sets {

  import opened StandardLibrary = StandardLibrary
  method {:extern ""SetToOrderedSequence""} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    decreases s
}

module Sorting {

  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering, LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow, SelectionSort, StandardLibrary, UInt


  import StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  predicate Reflexive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T :: 
      R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T :: 
      R(x, y) &&
      R(y, x) ==>
        x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T :: 
      R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    AntiSymmetric(R) &&
    StandardLibrary.Transitive(R) &&
    Connected(R)
  }

  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>)
    decreases x, y
  {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    n == |x| || (n != |y| && x[n] < y[n]) || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
    assert Reflexive(LexicographicByteSeqBelow) by {
      forall x: seq<uint8>, n: int | 0 <= n <= |x| {
        AboutLexicographicByteSeqBelowAux_Reflexive(x, n);
      }
    }
    assert AntiSymmetric(LexicographicByteSeqBelow) by {
      forall x: seq<uint8>, y: seq<uint8>, n: nat | n <= |x| && n <= |y| && x[..n] == y[..n] && LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n) {
        AboutLexicographicByteSeqBelowAux_AntiSymmetric(x, y, n);
      }
    }
    assert StandardLibrary.Transitive(LexicographicByteSeqBelow) by {
      forall x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat | n <= |x| && n <= |y| && n <= |z| && LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n) {
        AboutLexicographicByteSeqBelowAux_Transitive(x, y, z, n);
      }
    }
    assert Connected(LexicographicByteSeqBelow) by {
      forall x: seq<uint8>, y: seq<uint8>, n: nat | n <= |x| && n <= |y| {
        AboutLexicographicByteSeqBelowAux_Connected(x, y, n);
      }
    }
  }

  lemma /*{:_induction x, n}*/ AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, z, n}*/ AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  method SelectionSort<Data>(a: array<Data>, below: (Data, Data) -> bool)
    requires StandardLibrary.Transitive(below)
    requires Connected(below)
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i: int, j: int :: 0 <= i < j < a.Length ==> below(a[i], a[j])
    decreases a
  {
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall i: int, j: int :: 0 <= i < j < m ==> below(a[i], a[j])
      invariant forall i: int, j: int :: 0 <= i < m <= j < a.Length ==> below(a[i], a[j])
      decreases a.Length - m
    {
      var mindex, n := m, m + 1;
      while n < a.Length
        invariant m <= mindex < n <= a.Length
        invariant forall i: int :: m <= i < n ==> below(a[mindex], a[i])
        decreases a.Length - n
      {
        if !below(a[mindex], a[n]) {
          mindex := n;
        }
        n := n + 1;
      }
      a[m], a[mindex] := a[mindex], a[m];
      m := m + 1;
    }
  }
}

module Streams {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  class SeqReader<T> {
    ghost var Repr: set<object>
    const data: seq<T>
    var pos: nat

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      pos <= |data|
    }

    constructor (s: seq<T>)
      ensures pos == 0
      ensures data[..] == s
      ensures Valid() && fresh(Repr)
      decreases s
    {
      data := s;
      pos := 0;
      Repr := {this};
    }

    method ReadElements(n: nat) returns (elems: seq<T>)
      requires Valid()
      requires n + pos <= |data|
      modifies `pos
      ensures n == 0 ==> elems == []
      ensures n > 0 ==> elems == data[old(pos)..][..n]
      ensures pos == old(pos) + n
      ensures data == old(data)
      ensures Valid()
      decreases n
    {
      elems := data[pos..][..n];
      pos := pos + n;
      return elems;
    }

    method ReadExact(n: nat) returns (res: Result<seq<T>, string>)
      requires Valid()
      modifies `pos
      ensures n + old(pos) <= |data| <==> res.Success?
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? ==> pos == old(pos) + n
      ensures res.Success? ==> res.value == data[old(pos) .. old(pos) + n]
      ensures res.Failure? ==> n > |data| - pos
      ensures res.Failure? ==> pos == old(pos)
      ensures data == old(data)
      ensures Valid()
      decreases n
    {
      if n > |data| - pos {
        return Failure(""IO Error: Not enough elements left on stream."");
      } else {
        var elements := ReadElements(n);
        return Success(elements);
      }
    }
  }

  class ByteReader {
    ghost var Repr: set<object>
    const reader: SeqReader<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      reader in Repr &&
      reader.Repr <= Repr &&
      this !in reader.Repr &&
      reader.Valid()
    }

    constructor (s: seq<uint8>)
      ensures reader.data == s
      ensures reader.pos == 0
      ensures Valid() && fresh(Repr)
      decreases s
    {
      var mr := new SeqReader<uint8>(s);
      reader := mr;
      Repr := {this} + mr.Repr;
    }

    method ReadByte() returns (res: Result<uint8, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 1
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 1
      ensures old(reader.pos) + 1 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos)]
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(1);
      assert |bytes| == 1;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < n
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? && |res.value| == 0 ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + n
      ensures old(reader.pos) + n <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos) .. old(reader.pos) + n]
      ensures reader.data == old(reader.data)
      ensures Valid()
      decreases n
    {
      var bytes :- reader.ReadExact(n);
      assert |bytes| == n;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 2
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 2
      ensures old(reader.pos) + 2 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt16(reader.data[old(reader.pos) .. old(reader.pos) + 2])
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(2);
      assert |bytes| == 2;
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 4
      ensures old(reader.pos) + 4 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt32(reader.data[old(reader.pos) .. old(reader.pos) + 4])
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(4);
      assert |bytes| == 4;
      var n := SeqToUInt32(bytes);
      return Success(n);
    }

    method ReadUInt64() returns (res: Result<uint64, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 8
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 8
      ensures old(reader.pos) + 8 <= |old(reader.data)| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt64(reader.data[old(reader.pos) .. old(reader.pos) + 8])
      ensures reader.data == old(reader.data)
      ensures Valid()
    {
      var bytes :- reader.ReadExact(8);
      assert |bytes| == 8;
      var n := SeqToUInt64(bytes);
      return Success(n);
    }

    method IsDoneReading() returns (b: bool)
      requires Valid()
      ensures (b && |reader.data| - reader.pos == 0) || (!b && |reader.data| - reader.pos > 0)
      ensures Valid()
    {
      return |reader.data| == reader.pos;
    }

    method GetSizeRead() returns (n: nat)
      requires Valid()
      ensures n == reader.pos
      ensures Valid()
    {
      return reader.pos;
    }
  }

  class SeqWriter<T> {
    ghost var Repr: set<object>
    var data: seq<T>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr
    }

    constructor ()
      ensures data == []
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method WriteElements(elems: seq<T>) returns (n: nat)
      requires Valid()
      modifies `data
      ensures n == |data| - |old(data)| == |elems|
      ensures |elems| == 0 ==> data == old(data)
      ensures |elems| > 0 ==> data == old(data) + elems
      ensures elems == data[|data| - |elems|..]
      ensures Valid()
      decreases elems
    {
      data := data + elems;
      return |elems|;
    }
  }

  class ByteWriter {
    ghost var Repr: set<object>
    const writer: SeqWriter<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      writer in Repr &&
      writer.Repr <= Repr &&
      this !in writer.Repr &&
      writer.Valid()
    }

    constructor ()
      ensures writer.data == []
      ensures Valid() && fresh(Repr)
    {
      var mw := new SeqWriter<uint8>();
      writer := mw;
      Repr := {this} + mw.Repr;
    }

    method WriteByte(n: uint8) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures !unchanged(writer`data)
      ensures writer.data == old(writer.data) + [n]
      ensures r == 1
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements([n]);
    }

    method WriteBytes(s: seq<uint8>) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures |s| == 0 ==> unchanged(writer)
      ensures |s| > 0 ==> !unchanged(writer`data)
      ensures writer.data == old(writer.data) + s
      ensures r == |s|
      ensures Valid()
      decreases s
    {
      r := writer.WriteElements(s);
    }

    method WriteUInt16(n: uint16) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures !unchanged(writer`data)
      ensures writer.data == old(writer.data) + UInt16ToSeq(n)
      ensures r == 2
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt16ToSeq(n));
    }

    method WriteUInt32(n: uint32) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures !unchanged(writer`data)
      ensures writer.data == old(writer.data) + UInt32ToSeq(n)
      ensures r == 4
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt32ToSeq(n));
    }

    function method GetDataWritten(): (s: seq<uint8>)
      requires Valid()
      reads Repr
      ensures s == writer.data
      ensures Valid()
      decreases Repr
    {
      writer.data
    }

    function method GetSizeWritten(): (n: nat)
      requires Valid()
      reads Repr
      ensures n == |writer.data|
      ensures Valid()
      decreases Repr
    {
      |writer.data|
    }
  }
}

module Time {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  method {:extern ""TimeUtil.Time"", ""CurrentRelativeTime""} GetCurrent() returns (seconds: uint64)
}

module {:extern ""UTF8""} UTF8 {

  import opened Wrappers = Wrappers

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  method {:extern ""Encode""} Encode(s: string) returns (res: Result<ValidUTF8Bytes, string>)
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|
    decreases s

  method {:extern ""Decode""} Decode(b: ValidUTF8Bytes) returns (res: Result<string, string>)
    decreases b

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
    decreases s
  {
    0 <= s[0] <= 127
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
    decreases s
  {
    194 <= s[0] <= 223 &&
    128 <= s[1] <= 191
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
    decreases s
  {
    (s[0] == 224 && 160 <= s[1] <= 191 && 128 <= s[2] <= 191) || (225 <= s[0] <= 236 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191) || (s[0] == 237 && 128 <= s[1] <= 159 && 128 <= s[2] <= 191) || (238 <= s[0] <= 239 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191)
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
    decreases s
  {
    (s[0] == 240 && 144 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (241 <= s[0] <= 243 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (s[0] == 244 && 128 <= s[1] <= 143 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191)
  }

  predicate method ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r: seq<uint8> := a[lo .. hi]; if Uses1Byte(r) then ValidUTF8Range(a, lo + 1, hi) else if 2 <= |r| && Uses2Bytes(r) then ValidUTF8Range(a, lo + 2, hi) else if 3 <= |r| && Uses3Bytes(r) then ValidUTF8Range(a, lo + 3, hi) else 4 <= |r| && Uses4Bytes(r) && ValidUTF8Range(a, lo + 4, hi)
  }

  lemma /*{:_induction a, b, c, lo, hi}*/ ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
    if lo == hi {
    } else {
      ghost var r := b[lo .. hi];
      ghost var r' := (a + b + c)[|a| + lo .. |a| + hi];
      assert r == r';
      if Uses1Byte(r) {
        ValidUTF8Embed(a, b, c, lo + 1, hi);
      } else if 2 <= |r| && Uses2Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 2, hi);
      } else if 3 <= |r| && Uses3Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 3, hi);
      } else if 4 <= |r| && Uses4Bytes(r) {
        ValidUTF8Embed(a, b, c, lo + 4, hi);
      }
    }
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
    decreases s, t
  {
    ghost var lo := 0;
    while lo < |s|
      invariant lo <= |s|
      invariant ValidUTF8Range(s, lo, |s|)
      invariant ValidUTF8Range(s + t, 0, |s + t|) == ValidUTF8Range(s + t, lo, |s + t|)
      decreases |s| - lo
    {
      ghost var r := (s + t)[lo..];
      if Uses1Byte(r) {
        lo := lo + 1;
      } else if 2 <= |r| && Uses2Bytes(r) {
        lo := lo + 2;
      } else if 3 <= |r| && Uses3Bytes(r) {
        lo := lo + 3;
      } else if 4 <= |r| && Uses4Bytes(r) {
        lo := lo + 4;
      } else {
        assert false;
      }
    }
    calc {
      ValidUTF8Seq(s + t);
    ==
      ValidUTF8Range(s + t, 0, |s + t|);
    ==
      ValidUTF8Range(s + t, lo, |s + t|);
    ==
      {
        assert s + t == s + t + [] && lo == |s| && |s + t| == |s| + |t|;
      }
      ValidUTF8Range(s + t + [], |s|, |s| + |t|);
    ==
      {
        ValidUTF8Embed(s, t, [], 0, |t|);
      }
      ValidUTF8Range(t, 0, |t|);
    ==
      ValidUTF8Seq(t);
    ==
      true;
    }
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module Seq {

  import opened Wrappers = Wrappers

  import Math = Math
  function method First<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[0]
  }

  function method DropFirst<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[1..]
  }

  function method Last<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[|s| - 1]
  }

  function method DropLast<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[..|s| - 1]
  }

  lemma LemmaLast<T>(s: seq<T>)
    requires |s| > 0
    ensures DropLast(s) + [Last(s)] == s
    decreases s
  {
  }

  lemma LemmaAppendLast<T>(a: seq<T>, b: seq<T>)
    requires 0 < |a + b| && 0 < |b|
    ensures Last(a + b) == Last(b)
    decreases a, b
  {
  }

  lemma LemmaConcatIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == a + b + c
    decreases a, b, c
  {
  }

  predicate IsPrefix<T>(a: seq<T>, b: seq<T>)
    ensures IsPrefix(a, b) ==> |a| <= |b| && a == b[..|a|]
    decreases a, b
  {
    a <= b
  }

  predicate IsSuffix<T>(a: seq<T>, b: seq<T>)
    decreases a, b
  {
    |a| <= |b| &&
    a == b[|b| - |a|..]
  }

  lemma LemmaSplitAt<T>(s: seq<T>, pos: nat)
    requires pos < |s|
    ensures s[..pos] + s[pos..] == s
    decreases s, pos
  {
  }

  lemma LemmaElementFromSlice<T>(s: seq<T>, s': seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |s|
    requires s' == s[a .. b]
    requires a <= pos < b
    ensures pos - a < |s'|
    ensures s'[pos - a] == s[pos]
    decreases s, s', a, b, pos
  {
  }

  lemma LemmaSliceOfSlice<T>(s: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |s|
    requires 0 <= s2 <= e2 <= e1 - s1
    ensures s[s1 .. e1][s2 .. e2] == s[s1 + s2 .. s1 + e2]
    decreases s, s1, e1, s2, e2
  {
  }

  method ToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  function method {:opaque} {:fuel 0, 0} ToSet<T>(s: seq<T>): set<T>
    decreases s
  {
    set x: T {:trigger x in s} | x in s
  }

  lemma LemmaCardinalityOfSet<T>(s: seq<T>)
    ensures |ToSet(s)| <= |s|
    decreases s
  {
  }

  lemma LemmaCardinalityOfEmptySetIs0<T>(s: seq<T>)
    ensures |ToSet(s)| == 0 <==> |s| == 0
    decreases s
  {
  }

  predicate {:opaque} {:fuel 0, 0} HasNoDuplicates<T>(s: seq<T>)
    decreases s
  {
    forall i: int, j: int {:trigger s[i], s[j]} :: 
      0 <= i < |s| &&
      0 <= j < |s| &&
      i != j ==>
        s[i] != s[j]
  }

  lemma {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ LemmaNoDuplicatesInConcat<T>(a: seq<T>, b: seq<T>)
    requires HasNoDuplicates(a)
    requires HasNoDuplicates(b)
    requires multiset(a) !! multiset(b)
    ensures HasNoDuplicates(a + b)
    decreases a, b
  {
  }

  lemma LemmaCardinalityOfSetNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures |ToSet(s)| == |s|
    decreases s
  {
  }

  lemma LemmaNoDuplicatesCardinalityOfSet<T>(s: seq<T>)
    requires |ToSet(s)| == |s|
    ensures HasNoDuplicates(s)
    decreases s
  {
  }

  lemma LemmaMultisetHasNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures forall x: T {:trigger multiset(s)[x]} | x in multiset(s) :: multiset(s)[x] == 1
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} IndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: 0 <= j < i ==> s[j] != v
    decreases s
  {
    if s[0] == v then
      0
    else
      1 + IndexOf(s[1..], v)
  }

  function method {:opaque} {:fuel 0, 0} IndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: 0 <= j < o.value ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[0] == v then
      Some(0)
    else
      var o': Option<nat> := IndexOfOption(s[1..], v); if o'.Some? then Some(o'.value + 1) else None()
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: i < j < |s| ==> s[j] != v
    decreases s
  {
    if s[|s| - 1] == v then
      |s| - 1
    else
      LastIndexOf(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: o.value < j < |s| ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[|s| - 1] == v then
      Some(|s| - 1)
    else
      LastIndexOfOption(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} Remove<T>(s: seq<T>, pos: nat): (s': seq<T>)
    requires pos < |s|
    ensures |s'| == |s| - 1
    ensures forall i: int {:trigger s'[i], s[i]} | 0 <= i < pos :: s'[i] == s[i]
    ensures forall i: int {:trigger s'[i]} | pos <= i < |s| - 1 :: s'[i] == s[i + 1]
    decreases s, pos
  {
    s[..pos] + s[pos + 1..]
  }

  function method {:opaque} {:fuel 0, 0} RemoveValue<T(==)>(s: seq<T>, v: T): (s': seq<T>)
    ensures v !in s ==> s == s'
    ensures v in s ==> |multiset(s')| == |multiset(s)| - 1
    ensures v in s ==> multiset(s')[v] == multiset(s)[v] - 1
    ensures HasNoDuplicates(s) ==> HasNoDuplicates(s') && ToSet(s') == ToSet(s) - {v}
    decreases s
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in s then
      s
    else
      var i: nat := IndexOf(s, v); assert s == s[..i] + [v] + s[i + 1..]; s[..i] + s[i + 1..]
  }

  function method {:opaque} {:fuel 0, 0} Insert<T>(s: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |s|
    ensures |Insert(s, a, pos)| == |s| + 1
    ensures forall i: int {:trigger Insert(s, a, pos)[i], s[i]} :: 0 <= i < pos ==> Insert(s, a, pos)[i] == s[i]
    ensures forall i: int {:trigger s[i]} :: pos <= i < |s| ==> Insert(s, a, pos)[i + 1] == s[i]
    ensures Insert(s, a, pos)[pos] == a
    ensures multiset(Insert(s, a, pos)) == multiset(s) + multiset{a}
    decreases s, pos
  {
    assert s == s[..pos] + s[pos..];
    s[..pos] + [a] + s[pos..]
  }

  function method {:opaque} {:fuel 0, 0} Reverse<T>(s: seq<T>): (s': seq<T>)
    ensures |s'| == |s|
    ensures forall i: int {:trigger s'[i]} {:trigger s[|s| - i - 1]} :: 0 <= i < |s| ==> s'[i] == s[|s| - i - 1]
    decreases s
  {
    if s == [] then
      []
    else
      [s[|s| - 1]] + Reverse(s[0 .. |s| - 1])
  }

  function method {:opaque} {:fuel 0, 0} Repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat {:trigger s[i]} | i < |s| :: s[i] == v
    decreases length
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }

  function method {:opaque} {:fuel 0, 0} Unzip<A, B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(s).0| == |Unzip(s).1| == |s|
    ensures forall i: int {:trigger Unzip(s).0[i]} {:trigger Unzip(s).1[i]} :: 0 <= i < |s| ==> (Unzip(s).0[i], Unzip(s).1[i]) == s[i]
    decreases s
  {
    if |s| == 0 then
      ([], [])
    else
      var (a: seq<A>, b: seq<B>) := Unzip(DropLast(s)); (a + [Last(s).0], b + [Last(s).1])
  }

  function method {:opaque} {:fuel 0, 0} Zip<A, B>(a: seq<A>, b: seq<B>): seq<(A, B)>
    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i: int {:trigger Zip(a, b)[i]} :: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
    ensures Unzip(Zip(a, b)).0 == a
    ensures Unzip(Zip(a, b)).1 == b
    decreases a, b
  {
    if |a| == 0 then
      []
    else
      Zip(DropLast(a), DropLast(b)) + [(Last(a), Last(b))]
  }

  lemma /*{:_induction s}*/ LemmaZipOfUnzip<A, B>(s: seq<(A, B)>)
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} Max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Max(s) >= k
    ensures Max(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Max(s[0], Max(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMaxOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Max(a + b) >= Max(a)
    ensures Max(a + b) >= Max(b)
    ensures forall i: int {:trigger i in [Max(a + b)]} :: i in a + b ==> Max(a + b) >= i
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Min(s) <= k
    ensures Min(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Min(s[0], Min(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMinOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Min(a + b) <= Min(a)
    ensures Min(a + b) <= Min(b)
    ensures forall i: int {:trigger i in a + b} :: i in a + b ==> Min(a + b) <= i
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMax(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Max(s[from .. to]) <= Max(s)
    decreases s, from, to
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMin(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Min(s[from .. to]) >= Min(s)
    decreases s, from, to
  {
  }

  function method Flatten<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      s[0] + Flatten(s[1..])
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures Flatten(a + b) == Flatten(a) + Flatten(b)
    decreases a, b
  {
  }

  function method FlattenReverse<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      FlattenReverse(DropLast(s)) + Last(s)
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenReverseConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures FlattenReverse(a + b) == FlattenReverse(a) + FlattenReverse(b)
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenAndFlattenReverseAreEquivalent<T>(s: seq<seq<T>>)
    ensures Flatten(s) == FlattenReverse(s)
    decreases s
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthGeSingleElementLength<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |FlattenReverse(s)| >= |s[i]|
    decreases s, i
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthLeMul<T>(s: seq<seq<T>>, j: int)
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: |s[i]| <= j
    ensures |FlattenReverse(s)| <= |s| * j
    decreases s, j
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<T, R>(f: T ~> R, s: seq<T>): (result: seq<R>)
    requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures |result| == |s|
    ensures forall i: int {:trigger result[i]} :: 0 <= i < |s| ==> result[i] == f(s[i])
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      []
    else
      [f(s[0])] + Map(f, s[1..])
  }

  function method {:opaque} {:fuel 0, 0} MapWithResult<T, R, E>(f: T ~> Result<R, E>, s: seq<T>): (result: Result<seq<R>, E>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures result.Success? ==> |result.value| == |s| && forall i: int :: 0 <= i < |s| ==> f(s[i]).Success? && result.value[i] == f(s[i]).value
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      Success([])
    else
      var head: R :- f(s[0]); var tail: seq<R> :- MapWithResult(f, s[1..]); Success([head] + tail)
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaMapDistributesOverConcat<T, R>(f: T ~> R, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Map(f, a + b) == Map(f, a) + Map(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<T>(f: T ~> bool, s: seq<T>): (result: seq<T>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads f.reads
    ensures |result| <= |s|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    decreases set _x0: T, _o0: object? | _o0 in f.reads(_x0) :: _o0, s
  {
    if |s| == 0 then
      []
    else
      (if f(s[0]) then [s[0]] else []) + Filter(f, s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFilterDistributesOverConcat<T>(f: T ~> bool, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Filter(f, a + b) == Filter(f, a) + Filter(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldLeft<A, T>(f: (A, T) -> A, init: A, s: seq<T>): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      FoldLeft(f, f(init, s[0]), s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldLeftDistributesOverConcat<A, T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldLeft(f, init, a + b) == FoldLeft(f, FoldLeft(f, init, a), b)
    decreases a, b
  {
  }

  predicate InvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(b, [x] + xs) &&
      stp(b, x, b') ==>
        inv(b', xs)
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldLeft<A, B>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool, f: (B, A) -> B, b: B, xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b: B, a: A :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldRight<A, T>(f: (T, A) -> A, s: seq<T>, init: A): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      f(s[0], FoldRight(f, s[1..], init))
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldRight(f, a + b, init) == FoldRight(f, a, FoldRight(f, b, init))
    decreases a, b
  {
  }

  predicate InvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(xs, b) &&
      stp(x, b, b') ==>
        inv([x] + xs, b')
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldRight<A, B>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool, f: (A, B) -> B, b: B, xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a: A, b: B :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
    decreases xs
  {
  }
}

module Math {
  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Max(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      b
    else
      a
  }
}
")]

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T>
  {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T>
  {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }
        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }
    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }
      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }
      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T>
  {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T>
  {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t) || b.dict[t] < a.dict[t]) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          yield return key;
        }
      }
    }
  }

  public interface IMap<out U, out V>
  {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V>
  {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System.Tuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System.Tuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T>
  {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i]))
          return false;
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count  { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements
    {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m)
        return this;
      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m)
    {
      int startingElement = checked((int)m);
      if (startingElement == 0)
        return this;
      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int) lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }
  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get
      {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }
  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>();
      var toVisit = new Stack<ISequence<T>>();
      toVisit.Push(right);
      toVisit.Push(left);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        var cs = seq as ConcatSequence<T>;
        if (cs != null && cs.elmts.IsDefault) {
          toVisit.Push(cs.right);
          toVisit.Push(cs.left);
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B>
  {
    A Car { get; }
    B Cdr { get; }
  }
  public class Pair<A, B> : IPair<A, B>
  {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T>
  {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers
  {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) msg = "value out of range for a 32-bit int";
        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) msg = "value out of range for a 32-bit int";
        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString())
    {
    }
  }
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0,T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static Tuple2<T0,T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System.Tuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System.Tuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake2 { get { return true; } }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public class Tuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly Tuple0 theDefault = create();
    public static Tuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System.Tuple0> _TYPE = new Dafny.TypeDescriptor<_System.Tuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System.Tuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public class Tuple3<T0, T1, T2> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ")";
      return s;
    }
    public static Tuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System.Tuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System.Tuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static Tuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }







} // end of namespace _System
namespace Wrappers_Compile {

  public abstract class Option<T> {
    public Option() { }
    public static Option<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Option<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Option<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static Option<T> create_None() {
      return new Option_None<T>();
    }
    public static Option<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value; 
      }
    }
    public Wrappers_Compile.Result<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile.Option<T> _source0 = this;
      if (_source0.is_None) {
        return @Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _14040___mcc_h0 = ((Wrappers_Compile.Option_Some<T>)_source0).@value;
        T _14041_v = _14040___mcc_h0;
        return @Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_14041_v);
      }
    }
    public T UnwrapOr(T @default) {
      Wrappers_Compile.Option<T> _source1 = this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _14042___mcc_h0 = ((Wrappers_Compile.Option_Some<T>)_source1).@value;
        T _14043_v = _14042___mcc_h0;
        return _14043_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile.Option<__U> PropagateFailure<__U>() {
      return @Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public abstract class Result<T, R> {
    public Result() { }
    public static Result<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Result<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Result<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static Result<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static Result<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value; 
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error; 
      }
    }
    public Wrappers_Compile.Option<T> ToOption() {
      Wrappers_Compile.Result<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _14044___mcc_h0 = ((Wrappers_Compile.Result_Success<T, R>)_source2).@value;
        T _14045_s = _14044___mcc_h0;
        return @Wrappers_Compile.Option<T>.create_Some(_14045_s);
      } else {
        R _14046___mcc_h1 = ((Wrappers_Compile.Result_Failure<T, R>)_source2).error;
        R _14047_e = _14046___mcc_h1;
        return @Wrappers_Compile.Option<T>.create_None();
      }
    }
    public T UnwrapOr(T @default) {
      Wrappers_Compile.Result<T, R> _source3 = this;
      if (_source3.is_Success) {
        T _14048___mcc_h0 = ((Wrappers_Compile.Result_Success<T, R>)_source3).@value;
        T _14049_s = _14048___mcc_h0;
        return _14049_s;
      } else {
        R _14050___mcc_h1 = ((Wrappers_Compile.Result_Failure<T, R>)_source3).error;
        R _14051_e = _14050___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile.Result<__U, R> PropagateFailure<__U>() {
      return @Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public abstract class Outcome<E> {
    public Outcome() { }
    public static Outcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Outcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Outcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static Outcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static Outcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error; 
      }
    }
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile.Result<__U, E> PropagateFailure<__U>() {
      return @Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Outcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return @Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return @Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace StandardLibrary_mUInt_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool UInt8Less(byte a, byte b)
    {
      return (a) < (b);
    }
    public static Dafny.ISequence<byte> UInt16ToSeq(ushort x) {
      byte _14052_b0 = (byte)((ushort)((x) / (256)));
      byte _14053_b1 = (byte)((ushort)((x) % (256)));
      return Dafny.Sequence<byte>.FromElements(_14052_b0, _14053_b1);
    }
    public static ushort SeqToUInt16(Dafny.ISequence<byte> s) {
      ushort _14054_x0 = (ushort)(((ushort)((s).Select(BigInteger.Zero))) * (256));
      return (ushort)((_14054_x0) + ((ushort)((s).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<byte> UInt32ToSeq(uint x) {
      byte _14055_b0 = (byte)((x) / (16777216U));
      uint _14056_x0 = (x) - (((uint)(_14055_b0)) * (16777216U));
      byte _14057_b1 = (byte)((_14056_x0) / (65536U));
      uint _14058_x1 = (_14056_x0) - (((uint)(_14057_b1)) * (65536U));
      byte _14059_b2 = (byte)((_14058_x1) / (256U));
      byte _14060_b3 = (byte)((_14058_x1) % (256U));
      return Dafny.Sequence<byte>.FromElements(_14055_b0, _14057_b1, _14059_b2, _14060_b3);
    }
    public static uint SeqToUInt32(Dafny.ISequence<byte> s) {
      uint _14061_x0 = ((uint)((s).Select(BigInteger.Zero))) * (16777216U);
      uint _14062_x1 = (_14061_x0) + (((uint)((s).Select(BigInteger.One))) * (65536U));
      uint _14063_x2 = (_14062_x1) + (((uint)((s).Select(new BigInteger(2)))) * (256U));
      return (_14063_x2) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> UInt64ToSeq(ulong x) {
      byte _14064_b0 = (byte)((x) / (72057594037927936UL));
      ulong _14065_x0 = (x) - (((ulong)(_14064_b0)) * (72057594037927936UL));
      byte _14066_b1 = (byte)((_14065_x0) / (281474976710656UL));
      ulong _14067_x1 = (_14065_x0) - (((ulong)(_14066_b1)) * (281474976710656UL));
      byte _14068_b2 = (byte)((_14067_x1) / (1099511627776UL));
      ulong _14069_x2 = (_14067_x1) - (((ulong)(_14068_b2)) * (1099511627776UL));
      byte _14070_b3 = (byte)((_14069_x2) / (4294967296UL));
      ulong _14071_x3 = (_14069_x2) - (((ulong)(_14070_b3)) * (4294967296UL));
      byte _14072_b4 = (byte)((_14071_x3) / (16777216UL));
      ulong _14073_x4 = (_14071_x3) - (((ulong)(_14072_b4)) * (16777216UL));
      byte _14074_b5 = (byte)((_14073_x4) / (65536UL));
      ulong _14075_x5 = (_14073_x4) - (((ulong)(_14074_b5)) * (65536UL));
      byte _14076_b6 = (byte)((_14075_x5) / (256UL));
      byte _14077_b7 = (byte)((_14075_x5) % (256UL));
      return Dafny.Sequence<byte>.FromElements(_14064_b0, _14066_b1, _14068_b2, _14070_b3, _14072_b4, _14074_b5, _14076_b6, _14077_b7);
    }
    public static ulong SeqToUInt64(Dafny.ISequence<byte> s) {
      ulong _14078_x0 = ((ulong)((s).Select(BigInteger.Zero))) * (72057594037927936UL);
      ulong _14079_x1 = (_14078_x0) + (((ulong)((s).Select(BigInteger.One))) * (281474976710656UL));
      ulong _14080_x2 = (_14079_x1) + (((ulong)((s).Select(new BigInteger(2)))) * (1099511627776UL));
      ulong _14081_x3 = (_14080_x2) + (((ulong)((s).Select(new BigInteger(3)))) * (4294967296UL));
      ulong _14082_x4 = (_14081_x3) + (((ulong)((s).Select(new BigInteger(4)))) * (16777216UL));
      ulong _14083_x5 = (_14082_x4) + (((ulong)((s).Select(new BigInteger(5)))) * (65536UL));
      ulong _14084_x6 = (_14083_x5) + (((ulong)((s).Select(new BigInteger(6)))) * (256UL));
      ulong _14085_x = (_14084_x6) + ((ulong)((s).Select(new BigInteger(7))));
      return _14085_x;
    }
    public static BigInteger UINT32__LIMIT { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger UINT16__LIMIT { get {
      return new BigInteger(65536);
    } }
    public static BigInteger INT32__MAX__LIMIT { get {
      return new BigInteger(2147483648L);
    } }
    public static BigInteger INT64__MAX__LIMIT { get {
      return new BigInteger(9223372036854775808UL);
    } }
  }
} // end of namespace StandardLibrary_mUInt_Compile
namespace StandardLibrary_Compile {



  public partial class __default {
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> ss, Dafny.ISequence<__T> joiner)
    {
      Dafny.ISequence<__T> _14086___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ss).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_14086___accumulator, (ss).Select(BigInteger.Zero));
      } else {
        _14086___accumulator = Dafny.Sequence<__T>.Concat(_14086___accumulator, Dafny.Sequence<__T>.Concat((ss).Select(BigInteger.Zero), joiner));
        Dafny.ISequence<Dafny.ISequence<__T>> _in0 = (ss).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = joiner;
        ss = _in0;
        joiner = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _14087___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Wrappers_Compile.Option<BigInteger> _14088_i = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      if ((_14088_i).is_Some) {
        _14087___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_14087___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_14088_i).dtor_value)));
        Dafny.ISequence<__T> _in2 = (s).Drop(((_14088_i).dtor_value) + (BigInteger.One));
        __T _in3 = delim;
        s = _in2;
        delim = _in3;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_14087___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static Wrappers_Compile.Option<BigInteger> FindIndexMatching<__T>(Dafny.ISequence<__T> s, __T c, BigInteger i)
    {
      return StandardLibrary_Compile.__default.FindIndex<__T>(s, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_14089_c) => ((System.Func<__T, bool>)((_14090_x) => {
        return object.Equals(_14090_x, _14089_c);
      })))(c), i);
    }
    public static Wrappers_Compile.Option<BigInteger> FindIndex<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f, BigInteger i)
    {
    TAIL_CALL_START: ;
      if ((i) == (new BigInteger((s).Count))) {
        return @Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(i))) {
        return @Wrappers_Compile.Option<BigInteger>.create_Some(i);
      } else {
        Dafny.ISequence<__T> _in4 = s;
        Func<__T, bool> _in5 = f;
        BigInteger _in6 = (i) + (BigInteger.One);
        s = _in4;
        f = _in5;
        i = _in6;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f)
    {
      Dafny.ISequence<__T> _14091___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_14091___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) {
        _14091___accumulator = Dafny.Sequence<__T>.Concat(_14091___accumulator, Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in7 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in8 = f;
        s = _in7;
        f = _in8;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<__T> _in9 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in10 = f;
        s = _in9;
        f = _in10;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<__T> Fill<__T>(__T @value, BigInteger n)
    {
      return ((System.Func<Dafny.ISequence<__T>>) (() => {
        BigInteger dim0 = n;
        var arr0 = new __T[Dafny.Helpers.ToIntChecked(dim0,"C# array size must not be larger than max 32-bit int")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _14092___v0 = (BigInteger) i0;
          arr0[(int)(_14092___v0)] = @value;
        }
        return Dafny.Sequence<__T>.FromArray(arr0);
      }))();
    }
    public static __T[] SeqToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, __T> _arrayinit0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_14093_s) => ((System.Func<BigInteger, __T>)((_14094_i) => {
        return (_14093_s).Select(_14094_i);
      })))(s);
      for (var _arrayinit_00 = 0; _arrayinit_00 < new BigInteger(_nw0.Length); _arrayinit_00++) {
        _nw0[(int)(_arrayinit_00)] = _arrayinit0(_arrayinit_00);
      }
      a = _nw0;
      return a;
    }
    public static bool LexicographicLessOrEqual<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_14095_a, _14096_b, _14097_less) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((_14095_a).Count)) + (BigInteger.One)), false, (((_14098_k) => {
        return (((_14098_k).Sign != -1) && ((_14098_k) <= (new BigInteger((_14095_a).Count)))) && (StandardLibrary_Compile.__default.LexicographicLessOrEqualAux<__T>(_14095_a, _14096_b, _14097_less, _14098_k));
      }))))(a, b, less);
    }
    public static bool LexicographicLessOrEqualAux<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less, BigInteger lengthOfCommonPrefix)
    {
      return (((lengthOfCommonPrefix) <= (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<__T>, Dafny.ISequence<__T>, bool>>((_14099_lengthOfCommonPrefix, _14100_a, _14101_b) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, _14099_lengthOfCommonPrefix), true, (((_14102_i) => {
        return !(((_14102_i).Sign != -1) && ((_14102_i) < (_14099_lengthOfCommonPrefix))) || (object.Equals((_14100_a).Select(_14102_i), (_14101_b).Select(_14102_i)));
      }))))(lengthOfCommonPrefix, a, b))) && (((lengthOfCommonPrefix) == (new BigInteger((a).Count))) || (((lengthOfCommonPrefix) < (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)((a).Select(lengthOfCommonPrefix), (b).Select(lengthOfCommonPrefix)))));
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> SetToOrderedSequence<__T>(Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _14103___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      if ((s).Equals((Dafny.Set<Dafny.ISequence<__T>>.FromElements()))) {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_14103___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements());
      } else {
        return Dafny.Helpers.Let<int, Dafny.ISequence<Dafny.ISequence<__T>>>(0, _let_dummy_0 =>  {
          Dafny.ISequence<__T> _14104_a = Dafny.Sequence<__T>.Empty;
          foreach (Dafny.ISequence<__T> _assign_such_that_0 in (s).Elements) {
            _14104_a = (Dafny.ISequence<__T>)_assign_such_that_0;
            if (((s).Contains((_14104_a))) && (StandardLibrary_Compile.__default.IsMinimum<__T>(_14104_a, s, less))) {
              goto after__ASSIGN_SUCH_THAT_0;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 343)");
        after__ASSIGN_SUCH_THAT_0: ;
          return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(_14104_a), StandardLibrary_Compile.__default.SetToOrderedSequence<__T>(Dafny.Set<Dafny.ISequence<__T>>.Difference(s, Dafny.Set<Dafny.ISequence<__T>>.FromElements(_14104_a)), less));
        });
      }
    }
    public static bool IsMinimum<__T>(Dafny.ISequence<__T> a, Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      return ((s).Contains((a))) && (Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<__T>>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_14105_s, _14106_a, _14107_less) => Dafny.Helpers.Quantifier<Dafny.ISequence<__T>>((_14105_s).Elements, true, (((_14108_z) => {
        return !((_14105_s).Contains((_14108_z))) || (StandardLibrary_Compile.__default.LexicographicLessOrEqual<__T>(_14106_a, _14108_z, _14107_less));
      }))))(s, a, less));
    }
  }

} // end of namespace StandardLibrary_Compile
namespace EncryptionSuites {


  public class EncryptionAlgorithm {
    public readonly EncryptionSuites.AESMode mode;
    public EncryptionAlgorithm(EncryptionSuites.AESMode mode) {
      this.mode = mode;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.EncryptionAlgorithm;
      return oth != null && object.Equals(this.mode, oth.mode);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.mode));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.EncryptionAlgorithm.AES";
      s += "(";
      s += Dafny.Helpers.ToString(this.mode);
      s += ")";
      return s;
    }
    private static readonly EncryptionAlgorithm theDefault = create(EncryptionSuites.AESMode.Default());
    public static EncryptionAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptionSuites.EncryptionAlgorithm> _TYPE = new Dafny.TypeDescriptor<EncryptionSuites.EncryptionAlgorithm>(EncryptionSuites.EncryptionAlgorithm.Default());
    public static Dafny.TypeDescriptor<EncryptionSuites.EncryptionAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionAlgorithm create(EncryptionSuites.AESMode mode) {
      return new EncryptionAlgorithm(mode);
    }
    public bool is_AES { get { return true; } }
    public EncryptionSuites.AESMode dtor_mode {
      get {
        return this.mode;
      }
    }
  }

  public class AESMode {
    public AESMode() {
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.AESMode;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.AESMode.GCM";
      return s;
    }
    private static readonly AESMode theDefault = create();
    public static AESMode Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptionSuites.AESMode> _TYPE = new Dafny.TypeDescriptor<EncryptionSuites.AESMode>(EncryptionSuites.AESMode.Default());
    public static Dafny.TypeDescriptor<EncryptionSuites.AESMode> _TypeDescriptor() {
      return _TYPE;
    }
    public static AESMode create() {
      return new AESMode();
    }
    public bool is_GCM { get { return true; } }
    public static System.Collections.Generic.IEnumerable<AESMode> AllSingletonConstructors {
      get {
        yield return AESMode.create();
      }
    }
  }

  public class EncryptionSuite {
    public readonly EncryptionSuites.EncryptionAlgorithm alg;
    public readonly byte keyLen;
    public readonly byte tagLen;
    public readonly byte ivLen;
    public EncryptionSuite(EncryptionSuites.EncryptionAlgorithm alg, byte keyLen, byte tagLen, byte ivLen) {
      this.alg = alg;
      this.keyLen = keyLen;
      this.tagLen = tagLen;
      this.ivLen = ivLen;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.EncryptionSuite;
      return oth != null && object.Equals(this.alg, oth.alg) && this.keyLen == oth.keyLen && this.tagLen == oth.tagLen && this.ivLen == oth.ivLen;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.alg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyLen));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tagLen));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ivLen));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.EncryptionSuite.EncryptionSuite";
      s += "(";
      s += Dafny.Helpers.ToString(this.alg);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyLen);
      s += ", ";
      s += Dafny.Helpers.ToString(this.tagLen);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ivLen);
      s += ")";
      return s;
    }
    private static readonly EncryptionSuite theDefault = create(EncryptionSuites.EncryptionAlgorithm.Default(), 0, 0, 0);
    public static EncryptionSuite Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptionSuites.EncryptionSuite> _TYPE = new Dafny.TypeDescriptor<EncryptionSuites.EncryptionSuite>(EncryptionSuites.EncryptionSuite.Default());
    public static Dafny.TypeDescriptor<EncryptionSuites.EncryptionSuite> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionSuite create(EncryptionSuites.EncryptionAlgorithm alg, byte keyLen, byte tagLen, byte ivLen) {
      return new EncryptionSuite(alg, keyLen, tagLen, ivLen);
    }
    public bool is_EncryptionSuite { get { return true; } }
    public EncryptionSuites.EncryptionAlgorithm dtor_alg {
      get {
        return this.alg;
      }
    }
    public byte dtor_keyLen {
      get {
        return this.keyLen;
      }
    }
    public byte dtor_tagLen {
      get {
        return this.tagLen;
      }
    }
    public byte dtor_ivLen {
      get {
        return this.ivLen;
      }
    }
    public bool Valid() {
      EncryptionSuites.EncryptionAlgorithm _source4 = (this).dtor_alg;
      {
        EncryptionSuites.AESMode _14109___mcc_h0 = ((EncryptionSuites.EncryptionAlgorithm)_source4).mode;
        EncryptionSuites.AESMode _14110_mode = _14109___mcc_h0;
        return ((((EncryptionSuites.__default.AES__CIPHER__KEY__LENGTHS).Contains((new BigInteger((this).dtor_keyLen)))) && (((this).dtor_tagLen) == (EncryptionSuites.__default.AES__TAG__LEN))) && (((this).dtor_ivLen) == (EncryptionSuites.__default.AES__IV__LEN))) && (object.Equals(_14110_mode, @EncryptionSuites.AESMode.create()));
      }
    }
  }

  public partial class __default {
    public static byte AES__TAG__LEN { get {
      return (byte)(16);
    } }
    public static byte AES__IV__LEN { get {
      return (byte)(12);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__128 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 16, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__192 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 24, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__256 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 32, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static Dafny.ISet<BigInteger> AES__CIPHER__KEY__LENGTHS { get {
      return Dafny.Set<BigInteger>.FromElements(new BigInteger(32), new BigInteger(24), new BigInteger(16));
    } }
    public static BigInteger AES__MAX__KEY__LEN { get {
      return new BigInteger(32);
    } }
  }
} // end of namespace EncryptionSuites
namespace AESEncryption {





  public class EncryptionOutput {
    public readonly Dafny.ISequence<byte> cipherText;
    public readonly Dafny.ISequence<byte> authTag;
    public EncryptionOutput(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      this.cipherText = cipherText;
      this.authTag = authTag;
    }
    public override bool Equals(object other) {
      var oth = other as AESEncryption.EncryptionOutput;
      return oth != null && object.Equals(this.cipherText, oth.cipherText) && object.Equals(this.authTag, oth.authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cipherText));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AESEncryption_Compile.EncryptionOutput.EncryptionOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.cipherText);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authTag);
      s += ")";
      return s;
    }
    private static readonly EncryptionOutput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static EncryptionOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AESEncryption.EncryptionOutput> _TYPE = new Dafny.TypeDescriptor<AESEncryption.EncryptionOutput>(AESEncryption.EncryptionOutput.Default());
    public static Dafny.TypeDescriptor<AESEncryption.EncryptionOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionOutput create(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      return new EncryptionOutput(cipherText, authTag);
    }
    public bool is_EncryptionOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_cipherText {
      get {
        return this.cipherText;
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        return this.authTag;
      }
    }
  }

  public partial class __default {
    public static AESEncryption.EncryptionOutput EncryptionOutputFromByteSeq(Dafny.ISequence<byte> s, EncryptionSuites.EncryptionSuite encAlg)
    {
      return @AESEncryption.EncryptionOutput.create((s).Take((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLen))), (s).Drop((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLen))));
    }
    public static Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> AESEncrypt(EncryptionSuites.EncryptionSuite encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad)
    {
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>>.Default(AESEncryption.EncryptionOutput.Default());
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _out0;
      _out0 = AESEncryption.AES_GCM.AESEncryptExtern(encAlg, iv, key, msg, aad);
      res = _out0;
      if (((res).is_Success) && ((new BigInteger((((res).dtor_value).dtor_cipherText).Count)) != (new BigInteger((msg).Count)))) {
        res = @Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("AESEncrypt did not return cipherText of expected length"));
      }
      if (((res).is_Success) && ((new BigInteger((((res).dtor_value).dtor_authTag).Count)) != (new BigInteger((encAlg).dtor_tagLen)))) {
        res = @Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("AESEncryption did not return valid tag"));
      }
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> AESDecrypt(EncryptionSuites.EncryptionSuite encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out1;
      _out1 = AESEncryption.AES_GCM.AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);
      res = _out1;
      if (((res).is_Success) && ((new BigInteger((cipherTxt).Count)) != (new BigInteger(((res).dtor_value).Count)))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("AESDecrypt did not return plaintext of expected length"));
      }
      return res;
    }
  }
} // end of namespace AESEncryption
namespace CryptoDatatypes_Compile {

  public class DigestAlgorithm {
    public DigestAlgorithm() {
    }
    public override bool Equals(object other) {
      var oth = other as CryptoDatatypes_Compile.DigestAlgorithm;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "CryptoDatatypes_Compile.DigestAlgorithm.SHA_512";
      return s;
    }
    private static readonly DigestAlgorithm theDefault = create();
    public static DigestAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CryptoDatatypes_Compile.DigestAlgorithm> _TYPE = new Dafny.TypeDescriptor<CryptoDatatypes_Compile.DigestAlgorithm>(CryptoDatatypes_Compile.DigestAlgorithm.Default());
    public static Dafny.TypeDescriptor<CryptoDatatypes_Compile.DigestAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static DigestAlgorithm create() {
      return new DigestAlgorithm();
    }
    public bool is_SHA__512 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<DigestAlgorithm> AllSingletonConstructors {
      get {
        yield return DigestAlgorithm.create();
      }
    }
  }

} // end of namespace CryptoDatatypes_Compile
namespace ExternDigest {




} // end of namespace ExternDigest
namespace Digest_Compile {





  public partial class __default {
    public static BigInteger Length(CryptoDatatypes_Compile.DigestAlgorithm alg) {
      CryptoDatatypes_Compile.DigestAlgorithm _source5 = alg;
      {
        return new BigInteger(64);
      }
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Digest(CryptoDatatypes_Compile.DigestAlgorithm alg, Dafny.ISequence<byte> msg)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14111_result;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out2;
      _out2 = ExternDigest.__default.Digest(alg, msg);
      _14111_result = _out2;
      if (((_14111_result).is_Success) && ((new BigInteger(((_14111_result).dtor_value).Count)) != (Digest_Compile.__default.Length(alg)))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Incorrect length digest from ExternDigest."));
        return res;
      }
      res = _14111_result;
      return res;
      return res;
    }
  }
} // end of namespace Digest_Compile
namespace KeyDerivationAlgorithms {


  public abstract class KeyDerivationAlgorithm {
    public KeyDerivationAlgorithm() { }
    private static readonly KeyDerivationAlgorithm theDefault = create_HKDF__WITH__SHA__384();
    public static KeyDerivationAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TYPE = new Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm>(KeyDerivationAlgorithms.KeyDerivationAlgorithm.Default());
    public static Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static KeyDerivationAlgorithm create_HKDF__WITH__SHA__384() {
      return new KeyDerivationAlgorithm_HKDF__WITH__SHA__384();
    }
    public static KeyDerivationAlgorithm create_HKDF__WITH__SHA__256() {
      return new KeyDerivationAlgorithm_HKDF__WITH__SHA__256();
    }
    public static KeyDerivationAlgorithm create_IDENTITY() {
      return new KeyDerivationAlgorithm_IDENTITY();
    }
    public bool is_HKDF__WITH__SHA__384 { get { return this is KeyDerivationAlgorithm_HKDF__WITH__SHA__384; } }
    public bool is_HKDF__WITH__SHA__256 { get { return this is KeyDerivationAlgorithm_HKDF__WITH__SHA__256; } }
    public bool is_IDENTITY { get { return this is KeyDerivationAlgorithm_IDENTITY; } }
    public static System.Collections.Generic.IEnumerable<KeyDerivationAlgorithm> AllSingletonConstructors {
      get {
        yield return KeyDerivationAlgorithm.create_HKDF__WITH__SHA__384();
        yield return KeyDerivationAlgorithm.create_HKDF__WITH__SHA__256();
        yield return KeyDerivationAlgorithm.create_IDENTITY();
      }
    }
  }
  public class KeyDerivationAlgorithm_HKDF__WITH__SHA__384 : KeyDerivationAlgorithm {
    public KeyDerivationAlgorithm_HKDF__WITH__SHA__384() {
    }
    public override bool Equals(object other) {
      var oth = other as KeyDerivationAlgorithms.KeyDerivationAlgorithm_HKDF__WITH__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyDerivationAlgorithms_Compile.KeyDerivationAlgorithm.HKDF_WITH_SHA_384";
      return s;
    }
  }
  public class KeyDerivationAlgorithm_HKDF__WITH__SHA__256 : KeyDerivationAlgorithm {
    public KeyDerivationAlgorithm_HKDF__WITH__SHA__256() {
    }
    public override bool Equals(object other) {
      var oth = other as KeyDerivationAlgorithms.KeyDerivationAlgorithm_HKDF__WITH__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyDerivationAlgorithms_Compile.KeyDerivationAlgorithm.HKDF_WITH_SHA_256";
      return s;
    }
  }
  public class KeyDerivationAlgorithm_IDENTITY : KeyDerivationAlgorithm {
    public KeyDerivationAlgorithm_IDENTITY() {
    }
    public override bool Equals(object other) {
      var oth = other as KeyDerivationAlgorithms.KeyDerivationAlgorithm_IDENTITY;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyDerivationAlgorithms_Compile.KeyDerivationAlgorithm.IDENTITY";
      return s;
    }
  }

  public partial class HKDFAlgorithms {
    private static readonly KeyDerivationAlgorithms.KeyDerivationAlgorithm Witness = @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__384();
    public static KeyDerivationAlgorithms.KeyDerivationAlgorithm Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TYPE = new Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm>(KeyDerivationAlgorithms.HKDFAlgorithms.Default());
    public static Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class IdentityAlgorithm {
    private static readonly KeyDerivationAlgorithms.KeyDerivationAlgorithm Witness = @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY();
    public static KeyDerivationAlgorithms.KeyDerivationAlgorithm Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TYPE = new Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm>(KeyDerivationAlgorithms.IdentityAlgorithm.Default());
    public static Dafny.TypeDescriptor<KeyDerivationAlgorithms.KeyDerivationAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace KeyDerivationAlgorithms
namespace HMAC {




  public abstract class Digests {
    public Digests() { }
    private static readonly Digests theDefault = create_SHA__256();
    public static Digests Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<HMAC.Digests> _TYPE = new Dafny.TypeDescriptor<HMAC.Digests>(HMAC.Digests.Default());
    public static Dafny.TypeDescriptor<HMAC.Digests> _TypeDescriptor() {
      return _TYPE;
    }
    public static Digests create_SHA__256() {
      return new Digests_SHA__256();
    }
    public static Digests create_SHA__384() {
      return new Digests_SHA__384();
    }
    public bool is_SHA__256 { get { return this is Digests_SHA__256; } }
    public bool is_SHA__384 { get { return this is Digests_SHA__384; } }
    public static System.Collections.Generic.IEnumerable<Digests> AllSingletonConstructors {
      get {
        yield return Digests.create_SHA__256();
        yield return Digests.create_SHA__384();
      }
    }
  }
  public class Digests_SHA__256 : Digests {
    public Digests_SHA__256() {
    }
    public override bool Equals(object other) {
      var oth = other as HMAC.Digests_SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "HMAC_Compile.Digests.SHA_256";
      return s;
    }
  }
  public class Digests_SHA__384 : Digests {
    public Digests_SHA__384() {
    }
    public override bool Equals(object other) {
      var oth = other as HMAC.Digests_SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "HMAC_Compile.Digests.SHA_384";
      return s;
    }
  }


  public partial class __default {
    public static BigInteger GetHashLength(HMAC.Digests digest) {
      HMAC.Digests _source6 = digest;
      if (_source6.is_SHA__256) {
        return new BigInteger(32);
      } else {
        return new BigInteger(48);
      }
    }
  }
} // end of namespace HMAC
namespace HKDF_Compile {





  public partial class __default {
    public static HMAC.Digests GetHMACDigestFromHKDFAlgorithm(KeyDerivationAlgorithms.KeyDerivationAlgorithm algorithm) {
      KeyDerivationAlgorithms.KeyDerivationAlgorithm _source7 = algorithm;
      if (_source7.is_HKDF__WITH__SHA__384) {
        return @HMAC.Digests.create_SHA__384();
      } else {
        return @HMAC.Digests.create_SHA__256();
      }
    }
    public static Dafny.ISequence<byte> Extract(HMAC.HMac hmac, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> ikm)
    {
      Dafny.ISequence<byte> prk = Dafny.Sequence<byte>.Empty;
      (hmac).Init(salt);
      (hmac).BlockUpdate(ikm);
      Dafny.ISequence<byte> _out3;
      _out3 = (hmac).GetResult();
      prk = _out3;
      prk = prk;
      return prk;
      return prk;
    }
    public static Dafny.ISequence<byte> Expand(HMAC.HMac hmac, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, BigInteger expectedLength, HMAC.Digests digest)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      BigInteger _14112_hashLength;
      _14112_hashLength = HMAC.__default.GetHashLength(digest);
      BigInteger _14113_n;
      _14113_n = Dafny.Helpers.EuclideanDivision(((_14112_hashLength) + (expectedLength)) - (BigInteger.One), _14112_hashLength);
      (hmac).Init(prk);
      Dafny.ISequence<byte> _14114_t__prev;
      _14114_t__prev = Dafny.Sequence<byte>.FromElements();
      Dafny.ISequence<byte> _14115_t__n;
      _14115_t__n = _14114_t__prev;
      BigInteger _14116_i;
      _14116_i = BigInteger.One;
      while ((_14116_i) <= (_14113_n)) {
        (hmac).BlockUpdate(_14114_t__prev);
        (hmac).BlockUpdate(info);
        (hmac).BlockUpdate(Dafny.Sequence<byte>.FromElements((byte)(_14116_i)));
        Dafny.ISequence<byte> _out4;
        _out4 = (hmac).GetResult();
        _14114_t__prev = _out4;
        _14115_t__n = Dafny.Sequence<byte>.Concat(_14115_t__n, _14114_t__prev);
        _14116_i = (_14116_i) + (BigInteger.One);
      }
      okm = _14115_t__n;
      if ((expectedLength) < (new BigInteger((okm).Count))) {
        okm = (okm).Take(expectedLength);
      }
      return okm;
    }
    public static Dafny.ISequence<byte> Hkdf(KeyDerivationAlgorithms.KeyDerivationAlgorithm algorithm, Wrappers_Compile.Option<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, BigInteger L)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      if ((L).Sign == 0) {
        okm = Dafny.Sequence<byte>.FromElements();
        return okm;
      }
      HMAC.Digests _14117_digest;
      _14117_digest = HKDF_Compile.__default.GetHMACDigestFromHKDFAlgorithm(algorithm);
      HMAC.HMac _14118_hmac;
      HMAC.HMac _nw1 = new HMAC.HMac(_14117_digest);
      _14118_hmac = _nw1;
      BigInteger _14119_hashLength;
      _14119_hashLength = HMAC.__default.GetHashLength(_14117_digest);
      Dafny.ISequence<byte> _14120_nonEmptySalt = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Option<Dafny.ISequence<byte>> _source8 = salt;
      if (_source8.is_None) {
        {
          _14120_nonEmptySalt = StandardLibrary_Compile.__default.Fill<byte>(0, _14119_hashLength);
        }
      } else {
        Dafny.ISequence<byte> _14121___mcc_h0 = ((Wrappers_Compile.Option_Some<Dafny.ISequence<byte>>)_source8).@value;
        {
          Dafny.ISequence<byte> _14122_s = _14121___mcc_h0;
          _14120_nonEmptySalt = _14122_s;
        }
      }
      Dafny.ISequence<byte> _14123_prk;
      Dafny.ISequence<byte> _out5;
      _out5 = HKDF_Compile.__default.Extract(_14118_hmac, _14120_nonEmptySalt, ikm);
      _14123_prk = _out5;
      Dafny.ISequence<byte> _out6;
      _out6 = HKDF_Compile.__default.Expand(_14118_hmac, _14123_prk, info, L, _14117_digest);
      okm = _out6;
      return okm;
    }
  }
} // end of namespace HKDF_Compile
namespace ExternRandom {



} // end of namespace ExternRandom
namespace Random_Compile {





  public partial class __default {
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> GenerateBytes(int i)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14124_result;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out7;
      _out7 = ExternRandom.__default.GenerateBytes(i);
      _14124_result = _out7;
      if (((_14124_result).is_Success) && ((new BigInteger(((_14124_result).dtor_value).Count)) != (new BigInteger(i)))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Incorrect length from ExternRandom."));
        return res;
      }
      res = _14124_result;
      return res;
      return res;
    }
  }
} // end of namespace Random_Compile
namespace RSAEncryption {



  public abstract class PaddingMode {
    public PaddingMode() { }
    private static readonly PaddingMode theDefault = create_PKCS1();
    public static PaddingMode Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RSAEncryption.PaddingMode> _TYPE = new Dafny.TypeDescriptor<RSAEncryption.PaddingMode>(RSAEncryption.PaddingMode.Default());
    public static Dafny.TypeDescriptor<RSAEncryption.PaddingMode> _TypeDescriptor() {
      return _TYPE;
    }
    public static PaddingMode create_PKCS1() {
      return new PaddingMode_PKCS1();
    }
    public static PaddingMode create_OAEP__SHA1() {
      return new PaddingMode_OAEP__SHA1();
    }
    public static PaddingMode create_OAEP__SHA256() {
      return new PaddingMode_OAEP__SHA256();
    }
    public static PaddingMode create_OAEP__SHA384() {
      return new PaddingMode_OAEP__SHA384();
    }
    public static PaddingMode create_OAEP__SHA512() {
      return new PaddingMode_OAEP__SHA512();
    }
    public bool is_PKCS1 { get { return this is PaddingMode_PKCS1; } }
    public bool is_OAEP__SHA1 { get { return this is PaddingMode_OAEP__SHA1; } }
    public bool is_OAEP__SHA256 { get { return this is PaddingMode_OAEP__SHA256; } }
    public bool is_OAEP__SHA384 { get { return this is PaddingMode_OAEP__SHA384; } }
    public bool is_OAEP__SHA512 { get { return this is PaddingMode_OAEP__SHA512; } }
    public static System.Collections.Generic.IEnumerable<PaddingMode> AllSingletonConstructors {
      get {
        yield return PaddingMode.create_PKCS1();
        yield return PaddingMode.create_OAEP__SHA1();
        yield return PaddingMode.create_OAEP__SHA256();
        yield return PaddingMode.create_OAEP__SHA384();
        yield return PaddingMode.create_OAEP__SHA512();
      }
    }
  }
  public class PaddingMode_PKCS1 : PaddingMode {
    public PaddingMode_PKCS1() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_PKCS1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.PKCS1";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA1 : PaddingMode {
    public PaddingMode_OAEP__SHA1() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA1";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA256 : PaddingMode {
    public PaddingMode_OAEP__SHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA256";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA384 : PaddingMode {
    public PaddingMode_OAEP__SHA384() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA384";
      return s;
    }
  }
  public class PaddingMode_OAEP__SHA512 : PaddingMode {
    public PaddingMode_OAEP__SHA512() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.PaddingMode_OAEP__SHA512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.PaddingMode.OAEP_SHA512";
      return s;
    }
  }

  public partial class StrengthBits {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    public static readonly int Witness = (int)(new BigInteger(81));
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(RSAEncryption.StrengthBits.Witness);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface Key {
    Dafny.ISequence<byte> pem { get; }
  }
  public class _Companion_Key {
  }

  public partial class PrivateKey : RSAEncryption.Key {
    public PrivateKey() {
      this._pem = Dafny.Sequence<byte>.Empty;
    }
    public Dafny.ISequence<byte> _pem;public Dafny.ISequence<byte> pem { get {
      return this._pem;
    } }
    public void __ctor(Dafny.ISequence<byte> pem)
    {
      (this)._pem = pem;
    }
  }

  public partial class PublicKey : RSAEncryption.Key {
    public PublicKey() {
      this._pem = Dafny.Sequence<byte>.Empty;
    }
    public Dafny.ISequence<byte> _pem;public Dafny.ISequence<byte> pem { get {
      return this._pem;
    } }
    public void __ctor(Dafny.ISequence<byte> pem)
    {
      (this)._pem = pem;
    }
  }

  public partial class __default {
    public static void GenerateKeyPair(int strength, RSAEncryption.PaddingMode padding, out RSAEncryption.PublicKey publicKey, out RSAEncryption.PrivateKey privateKey)
    {
      publicKey = default(RSAEncryption.PublicKey);
      privateKey = default(RSAEncryption.PrivateKey);
      Dafny.ISequence<byte> _14125_pemPublic;
      Dafny.ISequence<byte> _14126_pemPrivate;
      Dafny.ISequence<byte> _out8;
      Dafny.ISequence<byte> _out9;
      RSAEncryption.RSA.GenerateKeyPairExtern(strength, padding, out _out8, out _out9);
      _14125_pemPublic = _out8;
      _14126_pemPrivate = _out9;
      RSAEncryption.PrivateKey _nw2 = new RSAEncryption.PrivateKey();
      _nw2.__ctor(_14126_pemPrivate);
      privateKey = _nw2;
      RSAEncryption.PublicKey _nw3 = new RSAEncryption.PublicKey();
      _nw3.__ctor(_14125_pemPublic);
      publicKey = _nw3;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Decrypt(RSAEncryption.PaddingMode padding, RSAEncryption.PrivateKey privateKey, Dafny.ISequence<byte> cipherText)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out10;
      _out10 = RSAEncryption.RSA.DecryptExtern(padding, (privateKey).pem, cipherText);
      res = _out10;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Encrypt(RSAEncryption.PaddingMode padding, RSAEncryption.PublicKey publicKey, Dafny.ISequence<byte> plaintextData)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out11;
      _out11 = RSAEncryption.RSA.EncryptExtern(padding, (publicKey).pem, plaintextData);
      res = _out11;
      return res;
    }
    public static BigInteger SHA1__HASH__BYTES { get {
      return new BigInteger(20);
    } }
    public static BigInteger SHA256__HASH__BYTES { get {
      return new BigInteger(32);
    } }
    public static BigInteger SHA384__HASH__BYTES { get {
      return new BigInteger(48);
    } }
    public static BigInteger SHA512__HASH__BYTES { get {
      return new BigInteger(64);
    } }
  }
} // end of namespace RSAEncryption
namespace Signature {




  public class SignatureKeyPair {
    public readonly Dafny.ISequence<byte> verificationKey;
    public readonly Dafny.ISequence<byte> signingKey;
    public SignatureKeyPair(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      this.verificationKey = verificationKey;
      this.signingKey = signingKey;
    }
    public override bool Equals(object other) {
      var oth = other as Signature.SignatureKeyPair;
      return oth != null && object.Equals(this.verificationKey, oth.verificationKey) && object.Equals(this.signingKey, oth.signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.SignatureKeyPair.SignatureKeyPair";
      s += "(";
      s += Dafny.Helpers.ToString(this.verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.signingKey);
      s += ")";
      return s;
    }
    private static readonly SignatureKeyPair theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static SignatureKeyPair Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Signature.SignatureKeyPair> _TYPE = new Dafny.TypeDescriptor<Signature.SignatureKeyPair>(Signature.SignatureKeyPair.Default());
    public static Dafny.TypeDescriptor<Signature.SignatureKeyPair> _TypeDescriptor() {
      return _TYPE;
    }
    public static SignatureKeyPair create(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return new SignatureKeyPair(verificationKey, signingKey);
    }
    public bool is_SignatureKeyPair { get { return true; } }
    public Dafny.ISequence<byte> dtor_verificationKey {
      get {
        return this.verificationKey;
      }
    }
    public Dafny.ISequence<byte> dtor_signingKey {
      get {
        return this.signingKey;
      }
    }
  }

  public abstract class ECDSAParams {
    public ECDSAParams() { }
    private static readonly ECDSAParams theDefault = create_ECDSA__P384();
    public static ECDSAParams Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Signature.ECDSAParams> _TYPE = new Dafny.TypeDescriptor<Signature.ECDSAParams>(Signature.ECDSAParams.Default());
    public static Dafny.TypeDescriptor<Signature.ECDSAParams> _TypeDescriptor() {
      return _TYPE;
    }
    public static ECDSAParams create_ECDSA__P384() {
      return new ECDSAParams_ECDSA__P384();
    }
    public static ECDSAParams create_ECDSA__P256() {
      return new ECDSAParams_ECDSA__P256();
    }
    public bool is_ECDSA__P384 { get { return this is ECDSAParams_ECDSA__P384; } }
    public bool is_ECDSA__P256 { get { return this is ECDSAParams_ECDSA__P256; } }
    public static System.Collections.Generic.IEnumerable<ECDSAParams> AllSingletonConstructors {
      get {
        yield return ECDSAParams.create_ECDSA__P384();
        yield return ECDSAParams.create_ECDSA__P256();
      }
    }
    public ushort SignatureLength() {
      Signature.ECDSAParams _source9 = this;
      if (_source9.is_ECDSA__P384) {
        return 103;
      } else {
        return 71;
      }
    }
    public BigInteger FieldSize() {
      Signature.ECDSAParams _source10 = this;
      if (_source10.is_ECDSA__P384) {
        return new BigInteger(49);
      } else {
        return new BigInteger(33);
      }
    }
  }
  public class ECDSAParams_ECDSA__P384 : ECDSAParams {
    public ECDSAParams_ECDSA__P384() {
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P384";
      return s;
    }
  }
  public class ECDSAParams_ECDSA__P256 : ECDSAParams {
    public ECDSAParams_ECDSA__P256() {
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P256";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> KeyGen(Signature.ECDSAParams s)
    {
      Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>>.Default(Signature.SignatureKeyPair.Default());
      Signature.SignatureKeyPair _14127_sigKeyPair = Signature.SignatureKeyPair.Default();
      Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> _14128_valueOrError0 = Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>>.Default(Signature.SignatureKeyPair.Default());
      Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> _out12;
      _out12 = Signature.ECDSA.ExternKeyGen(s);
      _14128_valueOrError0 = _out12;
      if ((_14128_valueOrError0).IsFailure()) {
        res = (_14128_valueOrError0).PropagateFailure<Signature.SignatureKeyPair>();
        return res;
      }
      _14127_sigKeyPair = (_14128_valueOrError0).Extract();
      if ((new BigInteger(((_14127_sigKeyPair).dtor_verificationKey).Count)) == ((s).FieldSize())) {
        res = @Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>>.create_Success(_14127_sigKeyPair);
        return res;
      } else {
        res = @Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Incorrect verification-key length from ExternKeyGen."));
        return res;
      }
      return res;
    }
  }
} // end of namespace Signature
namespace Amazon.KeyManagementService {


} // end of namespace Amazon.KeyManagementService
namespace UTF8 {



  public partial class ValidUTF8Bytes {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(UTF8.ValidUTF8Bytes.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsASCIIString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_14129_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_14129_s).Count)), true, (((_14130_i) => {
        return !(((_14130_i).Sign != -1) && ((_14130_i) < (new BigInteger((_14129_s).Count)))) || ((new BigInteger((_14129_s).Select(_14130_i))) < (new BigInteger(128)));
      }))))(s);
    }
    public static bool Uses1Byte(Dafny.ISequence<byte> s) {
      return ((0) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (127));
    }
    public static bool Uses2Bytes(Dafny.ISequence<byte> s) {
      return (((194) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (223))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)));
    }
    public static bool Uses3Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (224)) && (((160) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) || (((((225) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (236))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((s).Select(BigInteger.Zero)) == (237)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (159)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))))) || (((((238) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (239))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191))));
    }
    public static bool Uses4Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == (240)) && (((144) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191)))) || ((((((241) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= (243))) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (191)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))))) || ((((((s).Select(BigInteger.Zero)) == (244)) && (((128) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= (143)))) && (((128) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= (191)))) && (((128) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= (191))));
    }
    public static bool ValidUTF8Range(Dafny.ISequence<byte> a, BigInteger lo, BigInteger hi)
    {
      if ((lo) == (hi)) {
        return true;
      } else {
        Dafny.ISequence<byte> _14131_r = (a).Subsequence(lo, hi);
        if (UTF8.__default.Uses1Byte(_14131_r)) {
          return UTF8.__default.ValidUTF8Range(a, (lo) + (BigInteger.One), hi);
        } else if (((new BigInteger(2)) <= (new BigInteger((_14131_r).Count))) && (UTF8.__default.Uses2Bytes(_14131_r))) {
          return UTF8.__default.ValidUTF8Range(a, (lo) + (new BigInteger(2)), hi);
        } else if (((new BigInteger(3)) <= (new BigInteger((_14131_r).Count))) && (UTF8.__default.Uses3Bytes(_14131_r))) {
          return UTF8.__default.ValidUTF8Range(a, (lo) + (new BigInteger(3)), hi);
        } else {
          return (((new BigInteger(4)) <= (new BigInteger((_14131_r).Count))) && (UTF8.__default.Uses4Bytes(_14131_r))) && (UTF8.__default.ValidUTF8Range(a, (lo) + (new BigInteger(4)), hi));
        }
      }
    }
    public static bool ValidUTF8Seq(Dafny.ISequence<byte> s) {
      return UTF8.__default.ValidUTF8Range(s, BigInteger.Zero, new BigInteger((s).Count));
    }
  }
} // end of namespace UTF8
namespace Dafny.Aws.Crypto {












  public class DiscoveryFilter {
    public readonly Dafny.ISequence<char> accountId;
    public readonly Dafny.ISequence<char> partition;
    public DiscoveryFilter(Dafny.ISequence<char> accountId, Dafny.ISequence<char> partition) {
      this.accountId = accountId;
      this.partition = partition;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DiscoveryFilter;
      return oth != null && object.Equals(this.accountId, oth.accountId) && object.Equals(this.partition, oth.partition);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.accountId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.partition));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DiscoveryFilter.DiscoveryFilter";
      s += "(";
      s += Dafny.Helpers.ToString(this.accountId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.partition);
      s += ")";
      return s;
    }
    private static readonly DiscoveryFilter theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static DiscoveryFilter Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DiscoveryFilter> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DiscoveryFilter>(Dafny.Aws.Crypto.DiscoveryFilter.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DiscoveryFilter> _TypeDescriptor() {
      return _TYPE;
    }
    public static DiscoveryFilter create(Dafny.ISequence<char> accountId, Dafny.ISequence<char> partition) {
      return new DiscoveryFilter(accountId, partition);
    }
    public bool is_DiscoveryFilter { get { return true; } }
    public Dafny.ISequence<char> dtor_accountId {
      get {
        return this.accountId;
      }
    }
    public Dafny.ISequence<char> dtor_partition {
      get {
        return this.partition;
      }
    }
  }

  public class GetClientInput {
    public readonly Dafny.ISequence<char> region;
    public GetClientInput(Dafny.ISequence<char> region) {
      this.region = region;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetClientInput;
      return oth != null && object.Equals(this.region, oth.region);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.region));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetClientInput.GetClientInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.region);
      s += ")";
      return s;
    }
    private static readonly GetClientInput theDefault = create(Dafny.Sequence<char>.Empty);
    public static GetClientInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetClientInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetClientInput>(Dafny.Aws.Crypto.GetClientInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetClientInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetClientInput create(Dafny.ISequence<char> region) {
      return new GetClientInput(region);
    }
    public bool is_GetClientInput { get { return true; } }
    public Dafny.ISequence<char> dtor_region {
      get {
        return this.region;
      }
    }
  }

  public interface IKmsClient {
  }
  public class _Companion_IKmsClient {
  }

  public interface IClientSupplier {
    Dafny.Aws.Crypto.IKmsClient GetClient(Dafny.Aws.Crypto.GetClientInput input);
  }
  public class _Companion_IClientSupplier {
  }


  public class EncryptedDataKey {
    public readonly Dafny.ISequence<byte> keyProviderId;
    public readonly Dafny.ISequence<byte> keyProviderInfo;
    public readonly Dafny.ISequence<byte> ciphertext;
    public EncryptedDataKey(Dafny.ISequence<byte> keyProviderId, Dafny.ISequence<byte> keyProviderInfo, Dafny.ISequence<byte> ciphertext) {
      this.keyProviderId = keyProviderId;
      this.keyProviderInfo = keyProviderInfo;
      this.ciphertext = ciphertext;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.EncryptedDataKey;
      return oth != null && object.Equals(this.keyProviderId, oth.keyProviderId) && object.Equals(this.keyProviderInfo, oth.keyProviderInfo) && object.Equals(this.ciphertext, oth.ciphertext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyProviderId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyProviderInfo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.EncryptedDataKey.EncryptedDataKey";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyProviderId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyProviderInfo);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ciphertext);
      s += ")";
      return s;
    }
    private static readonly EncryptedDataKey theDefault = create(UTF8.ValidUTF8Bytes.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static EncryptedDataKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey>(Dafny.Aws.Crypto.EncryptedDataKey.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptedDataKey create(Dafny.ISequence<byte> keyProviderId, Dafny.ISequence<byte> keyProviderInfo, Dafny.ISequence<byte> ciphertext) {
      return new EncryptedDataKey(keyProviderId, keyProviderInfo, ciphertext);
    }
    public bool is_EncryptedDataKey { get { return true; } }
    public Dafny.ISequence<byte> dtor_keyProviderId {
      get {
        return this.keyProviderId;
      }
    }
    public Dafny.ISequence<byte> dtor_keyProviderInfo {
      get {
        return this.keyProviderInfo;
      }
    }
    public Dafny.ISequence<byte> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
  }

  public partial class ValidEncryptedDataKey {
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey>(Dafny.Aws.Crypto.EncryptedDataKey.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptedDataKey> _TypeDescriptor() {
      return _TYPE;
    }
  }


  public class EncryptionMaterials {
    public readonly Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey;
    public EncryptionMaterials(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey) {
      this.algorithmSuiteId = algorithmSuiteId;
      this.encryptionContext = encryptionContext;
      this.encryptedDataKeys = encryptedDataKeys;
      this.plaintextDataKey = plaintextDataKey;
      this.signingKey = signingKey;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.EncryptionMaterials;
      return oth != null && object.Equals(this.algorithmSuiteId, oth.algorithmSuiteId) && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.signingKey, oth.signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.EncryptionMaterials.EncryptionMaterials";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithmSuiteId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.signingKey);
      s += ")";
      return s;
    }
    private static readonly EncryptionMaterials theDefault = create(Dafny.Aws.Crypto.AlgorithmSuiteId.Default(), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Empty, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static EncryptionMaterials Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptionMaterials>(Dafny.Aws.Crypto.EncryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionMaterials create(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey) {
      return new EncryptionMaterials(algorithmSuiteId, encryptionContext, encryptedDataKeys, plaintextDataKey, signingKey);
    }
    public bool is_EncryptionMaterials { get { return true; } }
    public Dafny.Aws.Crypto.AlgorithmSuiteId dtor_algorithmSuiteId {
      get {
        return this.algorithmSuiteId;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_signingKey {
      get {
        return this.signingKey;
      }
    }
  }

  public class DecryptionMaterials {
    public readonly Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey;
    public DecryptionMaterials(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey) {
      this.algorithmSuiteId = algorithmSuiteId;
      this.encryptionContext = encryptionContext;
      this.plaintextDataKey = plaintextDataKey;
      this.verificationKey = verificationKey;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DecryptionMaterials;
      return oth != null && object.Equals(this.algorithmSuiteId, oth.algorithmSuiteId) && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.verificationKey, oth.verificationKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.verificationKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DecryptionMaterials.DecryptionMaterials";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithmSuiteId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.verificationKey);
      s += ")";
      return s;
    }
    private static readonly DecryptionMaterials theDefault = create(Dafny.Aws.Crypto.AlgorithmSuiteId.Default(), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static DecryptionMaterials Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptionMaterials>(Dafny.Aws.Crypto.DecryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptionMaterials create(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey) {
      return new DecryptionMaterials(algorithmSuiteId, encryptionContext, plaintextDataKey, verificationKey);
    }
    public bool is_DecryptionMaterials { get { return true; } }
    public Dafny.Aws.Crypto.AlgorithmSuiteId dtor_algorithmSuiteId {
      get {
        return this.algorithmSuiteId;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_verificationKey {
      get {
        return this.verificationKey;
      }
    }
  }

  public abstract class CommitmentPolicy {
    public CommitmentPolicy() { }
    private static readonly CommitmentPolicy theDefault = create_FORBID__ENCRYPT__FORBID__DECRYPT();
    public static CommitmentPolicy Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CommitmentPolicy> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CommitmentPolicy>(Dafny.Aws.Crypto.CommitmentPolicy.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CommitmentPolicy> _TypeDescriptor() {
      return _TYPE;
    }
    public static CommitmentPolicy create_FORBID__ENCRYPT__FORBID__DECRYPT() {
      return new CommitmentPolicy_FORBID__ENCRYPT__FORBID__DECRYPT();
    }
    public static CommitmentPolicy create_REQUIRE__ENCRYPT__ALLOW__DECRYPT() {
      return new CommitmentPolicy_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
    }
    public static CommitmentPolicy create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT() {
      return new CommitmentPolicy_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
    }
    public bool is_FORBID__ENCRYPT__FORBID__DECRYPT { get { return this is CommitmentPolicy_FORBID__ENCRYPT__FORBID__DECRYPT; } }
    public bool is_REQUIRE__ENCRYPT__ALLOW__DECRYPT { get { return this is CommitmentPolicy_REQUIRE__ENCRYPT__ALLOW__DECRYPT; } }
    public bool is_REQUIRE__ENCRYPT__REQUIRE__DECRYPT { get { return this is CommitmentPolicy_REQUIRE__ENCRYPT__REQUIRE__DECRYPT; } }
    public static System.Collections.Generic.IEnumerable<CommitmentPolicy> AllSingletonConstructors {
      get {
        yield return CommitmentPolicy.create_FORBID__ENCRYPT__FORBID__DECRYPT();
        yield return CommitmentPolicy.create_REQUIRE__ENCRYPT__ALLOW__DECRYPT();
        yield return CommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT();
      }
    }
  }
  public class CommitmentPolicy_FORBID__ENCRYPT__FORBID__DECRYPT : CommitmentPolicy {
    public CommitmentPolicy_FORBID__ENCRYPT__FORBID__DECRYPT() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CommitmentPolicy_FORBID__ENCRYPT__FORBID__DECRYPT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CommitmentPolicy.FORBID_ENCRYPT_FORBID_DECRYPT";
      return s;
    }
  }
  public class CommitmentPolicy_REQUIRE__ENCRYPT__ALLOW__DECRYPT : CommitmentPolicy {
    public CommitmentPolicy_REQUIRE__ENCRYPT__ALLOW__DECRYPT() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CommitmentPolicy_REQUIRE__ENCRYPT__ALLOW__DECRYPT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CommitmentPolicy.REQUIRE_ENCRYPT_ALLOW_DECRYPT";
      return s;
    }
  }
  public class CommitmentPolicy_REQUIRE__ENCRYPT__REQUIRE__DECRYPT : CommitmentPolicy {
    public CommitmentPolicy_REQUIRE__ENCRYPT__REQUIRE__DECRYPT() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CommitmentPolicy_REQUIRE__ENCRYPT__REQUIRE__DECRYPT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT";
      return s;
    }
  }

  public abstract class AesWrappingAlg {
    public AesWrappingAlg() { }
    private static readonly AesWrappingAlg theDefault = create_ALG__AES128__GCM__IV12__TAG16();
    public static AesWrappingAlg Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.AesWrappingAlg> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.AesWrappingAlg>(Dafny.Aws.Crypto.AesWrappingAlg.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.AesWrappingAlg> _TypeDescriptor() {
      return _TYPE;
    }
    public static AesWrappingAlg create_ALG__AES128__GCM__IV12__TAG16() {
      return new AesWrappingAlg_ALG__AES128__GCM__IV12__TAG16();
    }
    public static AesWrappingAlg create_ALG__AES192__GCM__IV12__TAG16() {
      return new AesWrappingAlg_ALG__AES192__GCM__IV12__TAG16();
    }
    public static AesWrappingAlg create_ALG__AES256__GCM__IV12__TAG16() {
      return new AesWrappingAlg_ALG__AES256__GCM__IV12__TAG16();
    }
    public bool is_ALG__AES128__GCM__IV12__TAG16 { get { return this is AesWrappingAlg_ALG__AES128__GCM__IV12__TAG16; } }
    public bool is_ALG__AES192__GCM__IV12__TAG16 { get { return this is AesWrappingAlg_ALG__AES192__GCM__IV12__TAG16; } }
    public bool is_ALG__AES256__GCM__IV12__TAG16 { get { return this is AesWrappingAlg_ALG__AES256__GCM__IV12__TAG16; } }
    public static System.Collections.Generic.IEnumerable<AesWrappingAlg> AllSingletonConstructors {
      get {
        yield return AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16();
        yield return AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16();
        yield return AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16();
      }
    }
  }
  public class AesWrappingAlg_ALG__AES128__GCM__IV12__TAG16 : AesWrappingAlg {
    public AesWrappingAlg_ALG__AES128__GCM__IV12__TAG16() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AesWrappingAlg_ALG__AES128__GCM__IV12__TAG16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AesWrappingAlg.ALG_AES128_GCM_IV12_TAG16";
      return s;
    }
  }
  public class AesWrappingAlg_ALG__AES192__GCM__IV12__TAG16 : AesWrappingAlg {
    public AesWrappingAlg_ALG__AES192__GCM__IV12__TAG16() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AesWrappingAlg_ALG__AES192__GCM__IV12__TAG16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AesWrappingAlg.ALG_AES192_GCM_IV12_TAG16";
      return s;
    }
  }
  public class AesWrappingAlg_ALG__AES256__GCM__IV12__TAG16 : AesWrappingAlg {
    public AesWrappingAlg_ALG__AES256__GCM__IV12__TAG16() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AesWrappingAlg_ALG__AES256__GCM__IV12__TAG16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AesWrappingAlg.ALG_AES256_GCM_IV12_TAG16";
      return s;
    }
  }

  public abstract class AlgorithmSuiteId {
    public AlgorithmSuiteId() { }
    private static readonly AlgorithmSuiteId theDefault = create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
    public static AlgorithmSuiteId Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.AlgorithmSuiteId> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.AlgorithmSuiteId>(Dafny.Aws.Crypto.AlgorithmSuiteId.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.AlgorithmSuiteId> _TypeDescriptor() {
      return _TYPE;
    }
    public static AlgorithmSuiteId create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF() {
      return new AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
    }
    public static AlgorithmSuiteId create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF() {
      return new AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
    }
    public static AlgorithmSuiteId create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF() {
      return new AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
    }
    public static AlgorithmSuiteId create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256() {
      return new AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
    }
    public static AlgorithmSuiteId create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256() {
      return new AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
    }
    public static AlgorithmSuiteId create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256() {
      return new AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
    }
    public static AlgorithmSuiteId create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256() {
      return new AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
    }
    public static AlgorithmSuiteId create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384() {
      return new AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
    }
    public static AlgorithmSuiteId create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384() {
      return new AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
    }
    public bool is_ALG__AES__128__GCM__IV12__TAG16__NO__KDF { get { return this is AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__NO__KDF; } }
    public bool is_ALG__AES__192__GCM__IV12__TAG16__NO__KDF { get { return this is AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__NO__KDF; } }
    public bool is_ALG__AES__256__GCM__IV12__TAG16__NO__KDF { get { return this is AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__NO__KDF; } }
    public bool is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256 { get { return this is AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256; } }
    public bool is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256 { get { return this is AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256; } }
    public bool is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256 { get { return this is AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256; } }
    public bool is_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256 { get { return this is AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256; } }
    public bool is_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get { return this is AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384; } }
    public bool is_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get { return this is AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384; } }
    public static System.Collections.Generic.IEnumerable<AlgorithmSuiteId> AllSingletonConstructors {
      get {
        yield return AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
        yield return AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
        yield return AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
        yield return AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
        yield return AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
        yield return AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
        yield return AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
        yield return AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
        yield return AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
      }
    }
  }
  public class AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__NO__KDF : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__NO__KDF() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__NO__KDF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_NO_KDF";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__NO__KDF : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__NO__KDF() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__NO__KDF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_NO_KDF";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__NO__KDF : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__NO__KDF() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__NO__KDF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_NO_KDF";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384";
      return s;
    }
  }
  public class AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 : AlgorithmSuiteId {
    public AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.AlgorithmSuiteId_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384";
      return s;
    }
  }

  public abstract class PaddingScheme {
    public PaddingScheme() { }
    private static readonly PaddingScheme theDefault = create_PKCS1();
    public static PaddingScheme Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.PaddingScheme> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.PaddingScheme>(Dafny.Aws.Crypto.PaddingScheme.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.PaddingScheme> _TypeDescriptor() {
      return _TYPE;
    }
    public static PaddingScheme create_PKCS1() {
      return new PaddingScheme_PKCS1();
    }
    public static PaddingScheme create_OAEP__SHA1__MGF1() {
      return new PaddingScheme_OAEP__SHA1__MGF1();
    }
    public static PaddingScheme create_OAEP__SHA256__MGF1() {
      return new PaddingScheme_OAEP__SHA256__MGF1();
    }
    public static PaddingScheme create_OAEP__SHA384__MGF1() {
      return new PaddingScheme_OAEP__SHA384__MGF1();
    }
    public static PaddingScheme create_OAEP__SHA512__MGF1() {
      return new PaddingScheme_OAEP__SHA512__MGF1();
    }
    public bool is_PKCS1 { get { return this is PaddingScheme_PKCS1; } }
    public bool is_OAEP__SHA1__MGF1 { get { return this is PaddingScheme_OAEP__SHA1__MGF1; } }
    public bool is_OAEP__SHA256__MGF1 { get { return this is PaddingScheme_OAEP__SHA256__MGF1; } }
    public bool is_OAEP__SHA384__MGF1 { get { return this is PaddingScheme_OAEP__SHA384__MGF1; } }
    public bool is_OAEP__SHA512__MGF1 { get { return this is PaddingScheme_OAEP__SHA512__MGF1; } }
    public static System.Collections.Generic.IEnumerable<PaddingScheme> AllSingletonConstructors {
      get {
        yield return PaddingScheme.create_PKCS1();
        yield return PaddingScheme.create_OAEP__SHA1__MGF1();
        yield return PaddingScheme.create_OAEP__SHA256__MGF1();
        yield return PaddingScheme.create_OAEP__SHA384__MGF1();
        yield return PaddingScheme.create_OAEP__SHA512__MGF1();
      }
    }
  }
  public class PaddingScheme_PKCS1 : PaddingScheme {
    public PaddingScheme_PKCS1() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PaddingScheme_PKCS1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PaddingScheme.PKCS1";
      return s;
    }
  }
  public class PaddingScheme_OAEP__SHA1__MGF1 : PaddingScheme {
    public PaddingScheme_OAEP__SHA1__MGF1() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PaddingScheme_OAEP__SHA1__MGF1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PaddingScheme.OAEP_SHA1_MGF1";
      return s;
    }
  }
  public class PaddingScheme_OAEP__SHA256__MGF1 : PaddingScheme {
    public PaddingScheme_OAEP__SHA256__MGF1() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PaddingScheme_OAEP__SHA256__MGF1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PaddingScheme.OAEP_SHA256_MGF1";
      return s;
    }
  }
  public class PaddingScheme_OAEP__SHA384__MGF1 : PaddingScheme {
    public PaddingScheme_OAEP__SHA384__MGF1() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PaddingScheme_OAEP__SHA384__MGF1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PaddingScheme.OAEP_SHA384_MGF1";
      return s;
    }
  }
  public class PaddingScheme_OAEP__SHA512__MGF1 : PaddingScheme {
    public PaddingScheme_OAEP__SHA512__MGF1() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PaddingScheme_OAEP__SHA512__MGF1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PaddingScheme.OAEP_SHA512_MGF1";
      return s;
    }
  }

  public class OnEncryptInput {
    public readonly Dafny.Aws.Crypto.EncryptionMaterials materials;
    public OnEncryptInput(Dafny.Aws.Crypto.EncryptionMaterials materials) {
      this.materials = materials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.OnEncryptInput;
      return oth != null && object.Equals(this.materials, oth.materials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.OnEncryptInput.OnEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.materials);
      s += ")";
      return s;
    }
    private static readonly OnEncryptInput theDefault = create(Dafny.Aws.Crypto.EncryptionMaterials.Default());
    public static OnEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptInput>(Dafny.Aws.Crypto.OnEncryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static OnEncryptInput create(Dafny.Aws.Crypto.EncryptionMaterials materials) {
      return new OnEncryptInput(materials);
    }
    public bool is_OnEncryptInput { get { return true; } }
    public Dafny.Aws.Crypto.EncryptionMaterials dtor_materials {
      get {
        return this.materials;
      }
    }
  }

  public class OnEncryptOutput {
    public readonly Dafny.Aws.Crypto.EncryptionMaterials materials;
    public OnEncryptOutput(Dafny.Aws.Crypto.EncryptionMaterials materials) {
      this.materials = materials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.OnEncryptOutput;
      return oth != null && object.Equals(this.materials, oth.materials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.OnEncryptOutput.OnEncryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.materials);
      s += ")";
      return s;
    }
    private static readonly OnEncryptOutput theDefault = create(Dafny.Aws.Crypto.EncryptionMaterials.Default());
    public static OnEncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptOutput>(Dafny.Aws.Crypto.OnEncryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnEncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static OnEncryptOutput create(Dafny.Aws.Crypto.EncryptionMaterials materials) {
      return new OnEncryptOutput(materials);
    }
    public bool is_OnEncryptOutput { get { return true; } }
    public Dafny.Aws.Crypto.EncryptionMaterials dtor_materials {
      get {
        return this.materials;
      }
    }
  }

  public class OnDecryptInput {
    public readonly Dafny.Aws.Crypto.DecryptionMaterials materials;
    public readonly Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys;
    public OnDecryptInput(Dafny.Aws.Crypto.DecryptionMaterials materials, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys) {
      this.materials = materials;
      this.encryptedDataKeys = encryptedDataKeys;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.OnDecryptInput;
      return oth != null && object.Equals(this.materials, oth.materials) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materials));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.OnDecryptInput.OnDecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.materials);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ")";
      return s;
    }
    private static readonly OnDecryptInput theDefault = create(Dafny.Aws.Crypto.DecryptionMaterials.Default(), Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Empty);
    public static OnDecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptInput>(Dafny.Aws.Crypto.OnDecryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static OnDecryptInput create(Dafny.Aws.Crypto.DecryptionMaterials materials, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys) {
      return new OnDecryptInput(materials, encryptedDataKeys);
    }
    public bool is_OnDecryptInput { get { return true; } }
    public Dafny.Aws.Crypto.DecryptionMaterials dtor_materials {
      get {
        return this.materials;
      }
    }
    public Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
  }

  public class OnDecryptOutput {
    public readonly Dafny.Aws.Crypto.DecryptionMaterials materials;
    public OnDecryptOutput(Dafny.Aws.Crypto.DecryptionMaterials materials) {
      this.materials = materials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.OnDecryptOutput;
      return oth != null && object.Equals(this.materials, oth.materials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.OnDecryptOutput.OnDecryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.materials);
      s += ")";
      return s;
    }
    private static readonly OnDecryptOutput theDefault = create(Dafny.Aws.Crypto.DecryptionMaterials.Default());
    public static OnDecryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptOutput>(Dafny.Aws.Crypto.OnDecryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.OnDecryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static OnDecryptOutput create(Dafny.Aws.Crypto.DecryptionMaterials materials) {
      return new OnDecryptOutput(materials);
    }
    public bool is_OnDecryptOutput { get { return true; } }
    public Dafny.Aws.Crypto.DecryptionMaterials dtor_materials {
      get {
        return this.materials;
      }
    }
  }

  public interface IKeyring {
    Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>> OnEncrypt(Dafny.Aws.Crypto.OnEncryptInput input);
    Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>> OnDecrypt(Dafny.Aws.Crypto.OnDecryptInput input);
  }
  public class _Companion_IKeyring {
  }

  public class CacheUsageMetadata {
    public readonly long messageUsage;
    public readonly long byteUsage;
    public CacheUsageMetadata(long messageUsage, long byteUsage) {
      this.messageUsage = messageUsage;
      this.byteUsage = byteUsage;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CacheUsageMetadata;
      return oth != null && this.messageUsage == oth.messageUsage && this.byteUsage == oth.byteUsage;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.messageUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.byteUsage));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CacheUsageMetadata.CacheUsageMetadata";
      s += "(";
      s += Dafny.Helpers.ToString(this.messageUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this.byteUsage);
      s += ")";
      return s;
    }
    private static readonly CacheUsageMetadata theDefault = create(0, 0);
    public static CacheUsageMetadata Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CacheUsageMetadata> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CacheUsageMetadata>(Dafny.Aws.Crypto.CacheUsageMetadata.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CacheUsageMetadata> _TypeDescriptor() {
      return _TYPE;
    }
    public static CacheUsageMetadata create(long messageUsage, long byteUsage) {
      return new CacheUsageMetadata(messageUsage, byteUsage);
    }
    public bool is_CacheUsageMetadata { get { return true; } }
    public long dtor_messageUsage {
      get {
        return this.messageUsage;
      }
    }
    public long dtor_byteUsage {
      get {
        return this.byteUsage;
      }
    }
  }

  public class EncryptEntry {
    public readonly Dafny.ISequence<byte> identifier;
    public readonly Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials;
    public readonly long creationTime;
    public readonly long expiryTime;
    public readonly Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata;
    public EncryptEntry(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials, long creationTime, long expiryTime, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      this.identifier = identifier;
      this.encryptionMaterials = encryptionMaterials;
      this.creationTime = creationTime;
      this.expiryTime = expiryTime;
      this.usageMetadata = usageMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.EncryptEntry;
      return oth != null && object.Equals(this.identifier, oth.identifier) && object.Equals(this.encryptionMaterials, oth.encryptionMaterials) && this.creationTime == oth.creationTime && this.expiryTime == oth.expiryTime && object.Equals(this.usageMetadata, oth.usageMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionMaterials));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.creationTime));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expiryTime));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.usageMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.EncryptEntry.EncryptEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionMaterials);
      s += ", ";
      s += Dafny.Helpers.ToString(this.creationTime);
      s += ", ";
      s += Dafny.Helpers.ToString(this.expiryTime);
      s += ", ";
      s += Dafny.Helpers.ToString(this.usageMetadata);
      s += ")";
      return s;
    }
    private static readonly EncryptEntry theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Aws.Crypto.EncryptionMaterials.Default(), 0, 0, Dafny.Aws.Crypto.CacheUsageMetadata.Default());
    public static EncryptEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptEntry> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptEntry>(Dafny.Aws.Crypto.EncryptEntry.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.EncryptEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptEntry create(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials, long creationTime, long expiryTime, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      return new EncryptEntry(identifier, encryptionMaterials, creationTime, expiryTime, usageMetadata);
    }
    public bool is_EncryptEntry { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
    public Dafny.Aws.Crypto.EncryptionMaterials dtor_encryptionMaterials {
      get {
        return this.encryptionMaterials;
      }
    }
    public long dtor_creationTime {
      get {
        return this.creationTime;
      }
    }
    public long dtor_expiryTime {
      get {
        return this.expiryTime;
      }
    }
    public Dafny.Aws.Crypto.CacheUsageMetadata dtor_usageMetadata {
      get {
        return this.usageMetadata;
      }
    }
  }

  public class DecryptEntry {
    public readonly Dafny.ISequence<byte> identifier;
    public readonly Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials;
    public readonly long creationTime;
    public readonly long expiryTime;
    public readonly Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata;
    public DecryptEntry(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials, long creationTime, long expiryTime, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      this.identifier = identifier;
      this.decryptionMaterials = decryptionMaterials;
      this.creationTime = creationTime;
      this.expiryTime = expiryTime;
      this.usageMetadata = usageMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DecryptEntry;
      return oth != null && object.Equals(this.identifier, oth.identifier) && object.Equals(this.decryptionMaterials, oth.decryptionMaterials) && this.creationTime == oth.creationTime && this.expiryTime == oth.expiryTime && object.Equals(this.usageMetadata, oth.usageMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.decryptionMaterials));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.creationTime));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expiryTime));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.usageMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DecryptEntry.DecryptEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this.decryptionMaterials);
      s += ", ";
      s += Dafny.Helpers.ToString(this.creationTime);
      s += ", ";
      s += Dafny.Helpers.ToString(this.expiryTime);
      s += ", ";
      s += Dafny.Helpers.ToString(this.usageMetadata);
      s += ")";
      return s;
    }
    private static readonly DecryptEntry theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Aws.Crypto.DecryptionMaterials.Default(), 0, 0, Dafny.Aws.Crypto.CacheUsageMetadata.Default());
    public static DecryptEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptEntry> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptEntry>(Dafny.Aws.Crypto.DecryptEntry.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptEntry create(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials, long creationTime, long expiryTime, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      return new DecryptEntry(identifier, decryptionMaterials, creationTime, expiryTime, usageMetadata);
    }
    public bool is_DecryptEntry { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
    public Dafny.Aws.Crypto.DecryptionMaterials dtor_decryptionMaterials {
      get {
        return this.decryptionMaterials;
      }
    }
    public long dtor_creationTime {
      get {
        return this.creationTime;
      }
    }
    public long dtor_expiryTime {
      get {
        return this.expiryTime;
      }
    }
    public Dafny.Aws.Crypto.CacheUsageMetadata dtor_usageMetadata {
      get {
        return this.usageMetadata;
      }
    }
  }

  public class PutEntryForEncryptInput {
    public readonly Dafny.ISequence<byte> identifier;
    public readonly Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials;
    public readonly Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata;
    public PutEntryForEncryptInput(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      this.identifier = identifier;
      this.encryptionMaterials = encryptionMaterials;
      this.usageMetadata = usageMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PutEntryForEncryptInput;
      return oth != null && object.Equals(this.identifier, oth.identifier) && object.Equals(this.encryptionMaterials, oth.encryptionMaterials) && object.Equals(this.usageMetadata, oth.usageMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionMaterials));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.usageMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PutEntryForEncryptInput.PutEntryForEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionMaterials);
      s += ", ";
      s += Dafny.Helpers.ToString(this.usageMetadata);
      s += ")";
      return s;
    }
    private static readonly PutEntryForEncryptInput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Aws.Crypto.EncryptionMaterials.Default(), Dafny.Aws.Crypto.CacheUsageMetadata.Default());
    public static PutEntryForEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptInput>(Dafny.Aws.Crypto.PutEntryForEncryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static PutEntryForEncryptInput create(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials, Dafny.Aws.Crypto.CacheUsageMetadata usageMetadata) {
      return new PutEntryForEncryptInput(identifier, encryptionMaterials, usageMetadata);
    }
    public bool is_PutEntryForEncryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
    public Dafny.Aws.Crypto.EncryptionMaterials dtor_encryptionMaterials {
      get {
        return this.encryptionMaterials;
      }
    }
    public Dafny.Aws.Crypto.CacheUsageMetadata dtor_usageMetadata {
      get {
        return this.usageMetadata;
      }
    }
  }

  public class PutEntryForEncryptOutput {
    public PutEntryForEncryptOutput() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PutEntryForEncryptOutput;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PutEntryForEncryptOutput.PutEntryForEncryptOutput";
      return s;
    }
    private static readonly PutEntryForEncryptOutput theDefault = create();
    public static PutEntryForEncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptOutput>(Dafny.Aws.Crypto.PutEntryForEncryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForEncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static PutEntryForEncryptOutput create() {
      return new PutEntryForEncryptOutput();
    }
    public bool is_PutEntryForEncryptOutput { get { return true; } }
    public static System.Collections.Generic.IEnumerable<PutEntryForEncryptOutput> AllSingletonConstructors {
      get {
        yield return PutEntryForEncryptOutput.create();
      }
    }
  }

  public class GetEntryForEncryptInput {
    public readonly Dafny.ISequence<byte> identifier;
    public GetEntryForEncryptInput(Dafny.ISequence<byte> identifier) {
      this.identifier = identifier;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEntryForEncryptInput;
      return oth != null && object.Equals(this.identifier, oth.identifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEntryForEncryptInput.GetEntryForEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ")";
      return s;
    }
    private static readonly GetEntryForEncryptInput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static GetEntryForEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptInput>(Dafny.Aws.Crypto.GetEntryForEncryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEntryForEncryptInput create(Dafny.ISequence<byte> identifier) {
      return new GetEntryForEncryptInput(identifier);
    }
    public bool is_GetEntryForEncryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
  }

  public class GetEntryForEncryptOutput {
    public readonly Dafny.Aws.Crypto.EncryptEntry cacheEntry;
    public GetEntryForEncryptOutput(Dafny.Aws.Crypto.EncryptEntry cacheEntry) {
      this.cacheEntry = cacheEntry;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEntryForEncryptOutput;
      return oth != null && object.Equals(this.cacheEntry, oth.cacheEntry);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cacheEntry));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEntryForEncryptOutput.GetEntryForEncryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.cacheEntry);
      s += ")";
      return s;
    }
    private static readonly GetEntryForEncryptOutput theDefault = create(Dafny.Aws.Crypto.EncryptEntry.Default());
    public static GetEntryForEncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptOutput>(Dafny.Aws.Crypto.GetEntryForEncryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForEncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEntryForEncryptOutput create(Dafny.Aws.Crypto.EncryptEntry cacheEntry) {
      return new GetEntryForEncryptOutput(cacheEntry);
    }
    public bool is_GetEntryForEncryptOutput { get { return true; } }
    public Dafny.Aws.Crypto.EncryptEntry dtor_cacheEntry {
      get {
        return this.cacheEntry;
      }
    }
  }

  public class PutEntryForDecryptInput {
    public readonly Dafny.ISequence<byte> identifier;
    public readonly Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials;
    public PutEntryForDecryptInput(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials) {
      this.identifier = identifier;
      this.decryptionMaterials = decryptionMaterials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PutEntryForDecryptInput;
      return oth != null && object.Equals(this.identifier, oth.identifier) && object.Equals(this.decryptionMaterials, oth.decryptionMaterials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.decryptionMaterials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PutEntryForDecryptInput.PutEntryForDecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this.decryptionMaterials);
      s += ")";
      return s;
    }
    private static readonly PutEntryForDecryptInput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Aws.Crypto.DecryptionMaterials.Default());
    public static PutEntryForDecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptInput>(Dafny.Aws.Crypto.PutEntryForDecryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static PutEntryForDecryptInput create(Dafny.ISequence<byte> identifier, Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials) {
      return new PutEntryForDecryptInput(identifier, decryptionMaterials);
    }
    public bool is_PutEntryForDecryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
    public Dafny.Aws.Crypto.DecryptionMaterials dtor_decryptionMaterials {
      get {
        return this.decryptionMaterials;
      }
    }
  }

  public class PutEntryForDecryptOutput {
    public PutEntryForDecryptOutput() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.PutEntryForDecryptOutput;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.PutEntryForDecryptOutput.PutEntryForDecryptOutput";
      return s;
    }
    private static readonly PutEntryForDecryptOutput theDefault = create();
    public static PutEntryForDecryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptOutput>(Dafny.Aws.Crypto.PutEntryForDecryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.PutEntryForDecryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static PutEntryForDecryptOutput create() {
      return new PutEntryForDecryptOutput();
    }
    public bool is_PutEntryForDecryptOutput { get { return true; } }
    public static System.Collections.Generic.IEnumerable<PutEntryForDecryptOutput> AllSingletonConstructors {
      get {
        yield return PutEntryForDecryptOutput.create();
      }
    }
  }

  public class GetEntryForDecryptInput {
    public readonly Dafny.ISequence<byte> identifier;
    public GetEntryForDecryptInput(Dafny.ISequence<byte> identifier) {
      this.identifier = identifier;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEntryForDecryptInput;
      return oth != null && object.Equals(this.identifier, oth.identifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEntryForDecryptInput.GetEntryForDecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ")";
      return s;
    }
    private static readonly GetEntryForDecryptInput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static GetEntryForDecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptInput>(Dafny.Aws.Crypto.GetEntryForDecryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEntryForDecryptInput create(Dafny.ISequence<byte> identifier) {
      return new GetEntryForDecryptInput(identifier);
    }
    public bool is_GetEntryForDecryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
  }

  public class GetEntryForDecryptOutput {
    public readonly Dafny.Aws.Crypto.DecryptEntry cacheEntry;
    public GetEntryForDecryptOutput(Dafny.Aws.Crypto.DecryptEntry cacheEntry) {
      this.cacheEntry = cacheEntry;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEntryForDecryptOutput;
      return oth != null && object.Equals(this.cacheEntry, oth.cacheEntry);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cacheEntry));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEntryForDecryptOutput.GetEntryForDecryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.cacheEntry);
      s += ")";
      return s;
    }
    private static readonly GetEntryForDecryptOutput theDefault = create(Dafny.Aws.Crypto.DecryptEntry.Default());
    public static GetEntryForDecryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptOutput>(Dafny.Aws.Crypto.GetEntryForDecryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEntryForDecryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEntryForDecryptOutput create(Dafny.Aws.Crypto.DecryptEntry cacheEntry) {
      return new GetEntryForDecryptOutput(cacheEntry);
    }
    public bool is_GetEntryForDecryptOutput { get { return true; } }
    public Dafny.Aws.Crypto.DecryptEntry dtor_cacheEntry {
      get {
        return this.cacheEntry;
      }
    }
  }

  public class DeleteEntryInput {
    public readonly Dafny.ISequence<byte> identifier;
    public DeleteEntryInput(Dafny.ISequence<byte> identifier) {
      this.identifier = identifier;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DeleteEntryInput;
      return oth != null && object.Equals(this.identifier, oth.identifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.identifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DeleteEntryInput.DeleteEntryInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.identifier);
      s += ")";
      return s;
    }
    private static readonly DeleteEntryInput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static DeleteEntryInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryInput>(Dafny.Aws.Crypto.DeleteEntryInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DeleteEntryInput create(Dafny.ISequence<byte> identifier) {
      return new DeleteEntryInput(identifier);
    }
    public bool is_DeleteEntryInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_identifier {
      get {
        return this.identifier;
      }
    }
  }

  public class DeleteEntryOutput {
    public DeleteEntryOutput() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DeleteEntryOutput;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DeleteEntryOutput.DeleteEntryOutput";
      return s;
    }
    private static readonly DeleteEntryOutput theDefault = create();
    public static DeleteEntryOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryOutput>(Dafny.Aws.Crypto.DeleteEntryOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DeleteEntryOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DeleteEntryOutput create() {
      return new DeleteEntryOutput();
    }
    public bool is_DeleteEntryOutput { get { return true; } }
    public static System.Collections.Generic.IEnumerable<DeleteEntryOutput> AllSingletonConstructors {
      get {
        yield return DeleteEntryOutput.create();
      }
    }
  }

  public interface ICryptoMaterialsCache {
    Dafny.Aws.Crypto.PutEntryForEncryptOutput PutEntryForEncrypt(Dafny.Aws.Crypto.PutEntryForEncryptInput input);
    Dafny.Aws.Crypto.GetEntryForEncryptOutput GetEntryForEncrypt(Dafny.Aws.Crypto.GetEntryForEncryptInput input);
    Dafny.Aws.Crypto.PutEntryForDecryptOutput PutEntryForDecrypt(Dafny.Aws.Crypto.PutEntryForDecryptInput input);
    Dafny.Aws.Crypto.GetEntryForDecryptOutput GetEntryForDecrypt(Dafny.Aws.Crypto.GetEntryForDecryptInput input);
    Dafny.Aws.Crypto.DeleteEntryOutput DeleteEntry(Dafny.Aws.Crypto.DeleteEntryInput input);
  }
  public class _Companion_ICryptoMaterialsCache {
  }

  public class GetEncryptionMaterialsInput {
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId;
    public readonly Wrappers_Compile.Option<long> maxPlaintextLength;
    public GetEncryptionMaterialsInput(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId, Wrappers_Compile.Option<long> maxPlaintextLength) {
      this.encryptionContext = encryptionContext;
      this.algorithmSuiteId = algorithmSuiteId;
      this.maxPlaintextLength = maxPlaintextLength;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEncryptionMaterialsInput;
      return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.algorithmSuiteId, oth.algorithmSuiteId) && object.Equals(this.maxPlaintextLength, oth.maxPlaintextLength);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.maxPlaintextLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEncryptionMaterialsInput.GetEncryptionMaterialsInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.maxPlaintextLength);
      s += ")";
      return s;
    }
    private static readonly GetEncryptionMaterialsInput theDefault = create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.Default(), Wrappers_Compile.Option<long>.Default());
    public static GetEncryptionMaterialsInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsInput>(Dafny.Aws.Crypto.GetEncryptionMaterialsInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEncryptionMaterialsInput create(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId, Wrappers_Compile.Option<long> maxPlaintextLength) {
      return new GetEncryptionMaterialsInput(encryptionContext, algorithmSuiteId, maxPlaintextLength);
    }
    public bool is_GetEncryptionMaterialsInput { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> dtor_algorithmSuiteId {
      get {
        return this.algorithmSuiteId;
      }
    }
    public Wrappers_Compile.Option<long> dtor_maxPlaintextLength {
      get {
        return this.maxPlaintextLength;
      }
    }
  }

  public class GetEncryptionMaterialsOutput {
    public readonly Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials;
    public GetEncryptionMaterialsOutput(Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials) {
      this.encryptionMaterials = encryptionMaterials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.GetEncryptionMaterialsOutput;
      return oth != null && object.Equals(this.encryptionMaterials, oth.encryptionMaterials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionMaterials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.GetEncryptionMaterialsOutput.GetEncryptionMaterialsOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionMaterials);
      s += ")";
      return s;
    }
    private static readonly GetEncryptionMaterialsOutput theDefault = create(Dafny.Aws.Crypto.EncryptionMaterials.Default());
    public static GetEncryptionMaterialsOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput>(Dafny.Aws.Crypto.GetEncryptionMaterialsOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static GetEncryptionMaterialsOutput create(Dafny.Aws.Crypto.EncryptionMaterials encryptionMaterials) {
      return new GetEncryptionMaterialsOutput(encryptionMaterials);
    }
    public bool is_GetEncryptionMaterialsOutput { get { return true; } }
    public Dafny.Aws.Crypto.EncryptionMaterials dtor_encryptionMaterials {
      get {
        return this.encryptionMaterials;
      }
    }
  }

  public class DecryptMaterialsInput {
    public readonly Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId;
    public readonly Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public DecryptMaterialsInput(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      this.algorithmSuiteId = algorithmSuiteId;
      this.encryptedDataKeys = encryptedDataKeys;
      this.encryptionContext = encryptionContext;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DecryptMaterialsInput;
      return oth != null && object.Equals(this.algorithmSuiteId, oth.algorithmSuiteId) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.encryptionContext, oth.encryptionContext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DecryptMaterialsInput.DecryptMaterialsInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithmSuiteId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ")";
      return s;
    }
    private static readonly DecryptMaterialsInput theDefault = create(Dafny.Aws.Crypto.AlgorithmSuiteId.Default(), Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Empty, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
    public static DecryptMaterialsInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsInput>(Dafny.Aws.Crypto.DecryptMaterialsInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptMaterialsInput create(Dafny.Aws.Crypto.AlgorithmSuiteId algorithmSuiteId, Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      return new DecryptMaterialsInput(algorithmSuiteId, encryptedDataKeys, encryptionContext);
    }
    public bool is_DecryptMaterialsInput { get { return true; } }
    public Dafny.Aws.Crypto.AlgorithmSuiteId dtor_algorithmSuiteId {
      get {
        return this.algorithmSuiteId;
      }
    }
    public Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
  }

  public class DecryptMaterialsOutput {
    public readonly Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials;
    public DecryptMaterialsOutput(Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials) {
      this.decryptionMaterials = decryptionMaterials;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.DecryptMaterialsOutput;
      return oth != null && object.Equals(this.decryptionMaterials, oth.decryptionMaterials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.decryptionMaterials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.DecryptMaterialsOutput.DecryptMaterialsOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.decryptionMaterials);
      s += ")";
      return s;
    }
    private static readonly DecryptMaterialsOutput theDefault = create(Dafny.Aws.Crypto.DecryptionMaterials.Default());
    public static DecryptMaterialsOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsOutput>(Dafny.Aws.Crypto.DecryptMaterialsOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.DecryptMaterialsOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptMaterialsOutput create(Dafny.Aws.Crypto.DecryptionMaterials decryptionMaterials) {
      return new DecryptMaterialsOutput(decryptionMaterials);
    }
    public bool is_DecryptMaterialsOutput { get { return true; } }
    public Dafny.Aws.Crypto.DecryptionMaterials dtor_decryptionMaterials {
      get {
        return this.decryptionMaterials;
      }
    }
  }

  public interface ICryptographicMaterialsManager {
    Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>> GetEncryptionMaterials(Dafny.Aws.Crypto.GetEncryptionMaterialsInput input);
    Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>> DecryptMaterials(Dafny.Aws.Crypto.DecryptMaterialsInput input);
  }
  public class _Companion_ICryptographicMaterialsManager {
  }

  public class CreateAwsKmsKeyringInput {
    public readonly Dafny.Aws.Crypto.IClientSupplier clientSupplier;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<char>> generator;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> keyIds;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens;
    public CreateAwsKmsKeyringInput(Dafny.Aws.Crypto.IClientSupplier clientSupplier, Wrappers_Compile.Option<Dafny.ISequence<char>> generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> keyIds, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens) {
      this.clientSupplier = clientSupplier;
      this.generator = generator;
      this.keyIds = keyIds;
      this.grantTokens = grantTokens;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateAwsKmsKeyringInput;
      return oth != null && this.clientSupplier == oth.clientSupplier && object.Equals(this.generator, oth.generator) && object.Equals(this.keyIds, oth.keyIds) && object.Equals(this.grantTokens, oth.grantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.clientSupplier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.generator));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyIds));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateAwsKmsKeyringInput.CreateAwsKmsKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.clientSupplier);
      s += ", ";
      s += Dafny.Helpers.ToString(this.generator);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyIds);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ")";
      return s;
    }
    private static readonly CreateAwsKmsKeyringInput theDefault = create(default(Dafny.Aws.Crypto.IClientSupplier), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static CreateAwsKmsKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateAwsKmsKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateAwsKmsKeyringInput>(Dafny.Aws.Crypto.CreateAwsKmsKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateAwsKmsKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateAwsKmsKeyringInput create(Dafny.Aws.Crypto.IClientSupplier clientSupplier, Wrappers_Compile.Option<Dafny.ISequence<char>> generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> keyIds, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens) {
      return new CreateAwsKmsKeyringInput(clientSupplier, generator, keyIds, grantTokens);
    }
    public bool is_CreateAwsKmsKeyringInput { get { return true; } }
    public Dafny.Aws.Crypto.IClientSupplier dtor_clientSupplier {
      get {
        return this.clientSupplier;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<char>> dtor_generator {
      get {
        return this.generator;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_keyIds {
      get {
        return this.keyIds;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
  }

  public class CreateMrkAwareStrictAwsKmsKeyringInput {
    public readonly Dafny.ISequence<char> kmsKeyId;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens;
    public readonly Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient;
    public CreateMrkAwareStrictAwsKmsKeyringInput(Dafny.ISequence<char> kmsKeyId, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient) {
      this.kmsKeyId = kmsKeyId;
      this.grantTokens = grantTokens;
      this.kmsClient = kmsClient;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput;
      return oth != null && object.Equals(this.kmsKeyId, oth.kmsKeyId) && object.Equals(this.grantTokens, oth.grantTokens) && this.kmsClient == oth.kmsClient;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.kmsKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.kmsClient));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateMrkAwareStrictAwsKmsKeyringInput.CreateMrkAwareStrictAwsKmsKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.kmsKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.kmsClient);
      s += ")";
      return s;
    }
    private static readonly CreateMrkAwareStrictAwsKmsKeyringInput theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), default(Amazon.KeyManagementService.IAmazonKeyManagementService));
    public static CreateMrkAwareStrictAwsKmsKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput>(Dafny.Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictAwsKmsKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateMrkAwareStrictAwsKmsKeyringInput create(Dafny.ISequence<char> kmsKeyId, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient) {
      return new CreateMrkAwareStrictAwsKmsKeyringInput(kmsKeyId, grantTokens, kmsClient);
    }
    public bool is_CreateMrkAwareStrictAwsKmsKeyringInput { get { return true; } }
    public Dafny.ISequence<char> dtor_kmsKeyId {
      get {
        return this.kmsKeyId;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Amazon.KeyManagementService.IAmazonKeyManagementService dtor_kmsClient {
      get {
        return this.kmsClient;
      }
    }
  }

  public class CreateMrkAwareStrictMultiKeyringInput {
    public readonly Wrappers_Compile.Option<Dafny.ISequence<char>> generator;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> kmsKeyIds;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens;
    public readonly Dafny.Aws.Crypto.IClientSupplier clientSupplier;
    public CreateMrkAwareStrictMultiKeyringInput(Wrappers_Compile.Option<Dafny.ISequence<char>> generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> kmsKeyIds, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Dafny.Aws.Crypto.IClientSupplier clientSupplier) {
      this.generator = generator;
      this.kmsKeyIds = kmsKeyIds;
      this.grantTokens = grantTokens;
      this.clientSupplier = clientSupplier;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput;
      return oth != null && object.Equals(this.generator, oth.generator) && object.Equals(this.kmsKeyIds, oth.kmsKeyIds) && object.Equals(this.grantTokens, oth.grantTokens) && this.clientSupplier == oth.clientSupplier;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.generator));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.kmsKeyIds));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.clientSupplier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateMrkAwareStrictMultiKeyringInput.CreateMrkAwareStrictMultiKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.generator);
      s += ", ";
      s += Dafny.Helpers.ToString(this.kmsKeyIds);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.clientSupplier);
      s += ")";
      return s;
    }
    private static readonly CreateMrkAwareStrictMultiKeyringInput theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), (Dafny.Aws.Crypto.IClientSupplier)null);
    public static CreateMrkAwareStrictMultiKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput>(Dafny.Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareStrictMultiKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateMrkAwareStrictMultiKeyringInput create(Wrappers_Compile.Option<Dafny.ISequence<char>> generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> kmsKeyIds, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Dafny.Aws.Crypto.IClientSupplier clientSupplier) {
      return new CreateMrkAwareStrictMultiKeyringInput(generator, kmsKeyIds, grantTokens, clientSupplier);
    }
    public bool is_CreateMrkAwareStrictMultiKeyringInput { get { return true; } }
    public Wrappers_Compile.Option<Dafny.ISequence<char>> dtor_generator {
      get {
        return this.generator;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_kmsKeyIds {
      get {
        return this.kmsKeyIds;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.Aws.Crypto.IClientSupplier dtor_clientSupplier {
      get {
        return this.clientSupplier;
      }
    }
  }

  public class CreateMrkAwareDiscoveryAwsKmsKeyringInput {
    public readonly Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient;
    public readonly Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens;
    public CreateMrkAwareDiscoveryAwsKmsKeyringInput(Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient, Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens) {
      this.kmsClient = kmsClient;
      this.discoveryFilter = discoveryFilter;
      this.grantTokens = grantTokens;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput;
      return oth != null && this.kmsClient == oth.kmsClient && object.Equals(this.discoveryFilter, oth.discoveryFilter) && object.Equals(this.grantTokens, oth.grantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.kmsClient));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.discoveryFilter));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateMrkAwareDiscoveryAwsKmsKeyringInput.CreateMrkAwareDiscoveryAwsKmsKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.kmsClient);
      s += ", ";
      s += Dafny.Helpers.ToString(this.discoveryFilter);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ")";
      return s;
    }
    private static readonly CreateMrkAwareDiscoveryAwsKmsKeyringInput theDefault = create(default(Amazon.KeyManagementService.IAmazonKeyManagementService), Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static CreateMrkAwareDiscoveryAwsKmsKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput>(Dafny.Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryAwsKmsKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateMrkAwareDiscoveryAwsKmsKeyringInput create(Amazon.KeyManagementService.IAmazonKeyManagementService kmsClient, Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens) {
      return new CreateMrkAwareDiscoveryAwsKmsKeyringInput(kmsClient, discoveryFilter, grantTokens);
    }
    public bool is_CreateMrkAwareDiscoveryAwsKmsKeyringInput { get { return true; } }
    public Amazon.KeyManagementService.IAmazonKeyManagementService dtor_kmsClient {
      get {
        return this.kmsClient;
      }
    }
    public Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> dtor_discoveryFilter {
      get {
        return this.discoveryFilter;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
  }

  public class CreateMrkAwareDiscoveryMultiKeyringInput {
    public readonly Dafny.ISequence<Dafny.ISequence<char>> regions;
    public readonly Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens;
    public readonly Dafny.Aws.Crypto.IClientSupplier clientSupplier;
    public CreateMrkAwareDiscoveryMultiKeyringInput(Dafny.ISequence<Dafny.ISequence<char>> regions, Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Dafny.Aws.Crypto.IClientSupplier clientSupplier) {
      this.regions = regions;
      this.discoveryFilter = discoveryFilter;
      this.grantTokens = grantTokens;
      this.clientSupplier = clientSupplier;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput;
      return oth != null && object.Equals(this.regions, oth.regions) && object.Equals(this.discoveryFilter, oth.discoveryFilter) && object.Equals(this.grantTokens, oth.grantTokens) && this.clientSupplier == oth.clientSupplier;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.regions));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.discoveryFilter));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.clientSupplier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateMrkAwareDiscoveryMultiKeyringInput.CreateMrkAwareDiscoveryMultiKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.regions);
      s += ", ";
      s += Dafny.Helpers.ToString(this.discoveryFilter);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.clientSupplier);
      s += ")";
      return s;
    }
    private static readonly CreateMrkAwareDiscoveryMultiKeyringInput theDefault = create(Dafny.Sequence<Dafny.ISequence<char>>.Empty, Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), (Dafny.Aws.Crypto.IClientSupplier)null);
    public static CreateMrkAwareDiscoveryMultiKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput>(Dafny.Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMrkAwareDiscoveryMultiKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateMrkAwareDiscoveryMultiKeyringInput create(Dafny.ISequence<Dafny.ISequence<char>> regions, Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> discoveryFilter, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> grantTokens, Dafny.Aws.Crypto.IClientSupplier clientSupplier) {
      return new CreateMrkAwareDiscoveryMultiKeyringInput(regions, discoveryFilter, grantTokens, clientSupplier);
    }
    public bool is_CreateMrkAwareDiscoveryMultiKeyringInput { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_regions {
      get {
        return this.regions;
      }
    }
    public Wrappers_Compile.Option<Dafny.Aws.Crypto.DiscoveryFilter> dtor_discoveryFilter {
      get {
        return this.discoveryFilter;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.Aws.Crypto.IClientSupplier dtor_clientSupplier {
      get {
        return this.clientSupplier;
      }
    }
  }

  public class CreateMultiKeyringInput {
    public readonly Dafny.Aws.Crypto.IKeyring generator;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>> childKeyrings;
    public CreateMultiKeyringInput(Dafny.Aws.Crypto.IKeyring generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>> childKeyrings) {
      this.generator = generator;
      this.childKeyrings = childKeyrings;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateMultiKeyringInput;
      return oth != null && this.generator == oth.generator && object.Equals(this.childKeyrings, oth.childKeyrings);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.generator));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.childKeyrings));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateMultiKeyringInput.CreateMultiKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.generator);
      s += ", ";
      s += Dafny.Helpers.ToString(this.childKeyrings);
      s += ")";
      return s;
    }
    private static readonly CreateMultiKeyringInput theDefault = create((Dafny.Aws.Crypto.IKeyring)null, Wrappers_Compile.Option<Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>>.Default());
    public static CreateMultiKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMultiKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMultiKeyringInput>(Dafny.Aws.Crypto.CreateMultiKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateMultiKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateMultiKeyringInput create(Dafny.Aws.Crypto.IKeyring generator, Wrappers_Compile.Option<Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>> childKeyrings) {
      return new CreateMultiKeyringInput(generator, childKeyrings);
    }
    public bool is_CreateMultiKeyringInput { get { return true; } }
    public Dafny.Aws.Crypto.IKeyring dtor_generator {
      get {
        return this.generator;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<Dafny.Aws.Crypto.IKeyring>> dtor_childKeyrings {
      get {
        return this.childKeyrings;
      }
    }
  }

  public class CreateRawAesKeyringInput {
    public readonly Dafny.ISequence<char> keyNamespace;
    public readonly Dafny.ISequence<char> keyName;
    public readonly Dafny.ISequence<byte> wrappingKey;
    public readonly Dafny.Aws.Crypto.AesWrappingAlg wrappingAlg;
    public CreateRawAesKeyringInput(Dafny.ISequence<char> keyNamespace, Dafny.ISequence<char> keyName, Dafny.ISequence<byte> wrappingKey, Dafny.Aws.Crypto.AesWrappingAlg wrappingAlg) {
      this.keyNamespace = keyNamespace;
      this.keyName = keyName;
      this.wrappingKey = wrappingKey;
      this.wrappingAlg = wrappingAlg;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateRawAesKeyringInput;
      return oth != null && object.Equals(this.keyNamespace, oth.keyNamespace) && object.Equals(this.keyName, oth.keyName) && object.Equals(this.wrappingKey, oth.wrappingKey) && object.Equals(this.wrappingAlg, oth.wrappingAlg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyNamespace));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.wrappingKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.wrappingAlg));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateRawAesKeyringInput.CreateRawAesKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyNamespace);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.wrappingKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.wrappingAlg);
      s += ")";
      return s;
    }
    private static readonly CreateRawAesKeyringInput theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Aws.Crypto.AesWrappingAlg.Default());
    public static CreateRawAesKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawAesKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawAesKeyringInput>(Dafny.Aws.Crypto.CreateRawAesKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawAesKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateRawAesKeyringInput create(Dafny.ISequence<char> keyNamespace, Dafny.ISequence<char> keyName, Dafny.ISequence<byte> wrappingKey, Dafny.Aws.Crypto.AesWrappingAlg wrappingAlg) {
      return new CreateRawAesKeyringInput(keyNamespace, keyName, wrappingKey, wrappingAlg);
    }
    public bool is_CreateRawAesKeyringInput { get { return true; } }
    public Dafny.ISequence<char> dtor_keyNamespace {
      get {
        return this.keyNamespace;
      }
    }
    public Dafny.ISequence<char> dtor_keyName {
      get {
        return this.keyName;
      }
    }
    public Dafny.ISequence<byte> dtor_wrappingKey {
      get {
        return this.wrappingKey;
      }
    }
    public Dafny.Aws.Crypto.AesWrappingAlg dtor_wrappingAlg {
      get {
        return this.wrappingAlg;
      }
    }
  }

  public class CreateRawRsaKeyringInput {
    public readonly Dafny.ISequence<char> keyNamespace;
    public readonly Dafny.ISequence<char> keyName;
    public readonly Dafny.Aws.Crypto.PaddingScheme paddingScheme;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> publicKey;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> privateKey;
    public CreateRawRsaKeyringInput(Dafny.ISequence<char> keyNamespace, Dafny.ISequence<char> keyName, Dafny.Aws.Crypto.PaddingScheme paddingScheme, Wrappers_Compile.Option<Dafny.ISequence<byte>> publicKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> privateKey) {
      this.keyNamespace = keyNamespace;
      this.keyName = keyName;
      this.paddingScheme = paddingScheme;
      this.publicKey = publicKey;
      this.privateKey = privateKey;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateRawRsaKeyringInput;
      return oth != null && object.Equals(this.keyNamespace, oth.keyNamespace) && object.Equals(this.keyName, oth.keyName) && object.Equals(this.paddingScheme, oth.paddingScheme) && object.Equals(this.publicKey, oth.publicKey) && object.Equals(this.privateKey, oth.privateKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyNamespace));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.paddingScheme));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.publicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.privateKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateRawRsaKeyringInput.CreateRawRsaKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyNamespace);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyName);
      s += ", ";
      s += Dafny.Helpers.ToString(this.paddingScheme);
      s += ", ";
      s += Dafny.Helpers.ToString(this.publicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.privateKey);
      s += ")";
      return s;
    }
    private static readonly CreateRawRsaKeyringInput theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Aws.Crypto.PaddingScheme.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static CreateRawRsaKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawRsaKeyringInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawRsaKeyringInput>(Dafny.Aws.Crypto.CreateRawRsaKeyringInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateRawRsaKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateRawRsaKeyringInput create(Dafny.ISequence<char> keyNamespace, Dafny.ISequence<char> keyName, Dafny.Aws.Crypto.PaddingScheme paddingScheme, Wrappers_Compile.Option<Dafny.ISequence<byte>> publicKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> privateKey) {
      return new CreateRawRsaKeyringInput(keyNamespace, keyName, paddingScheme, publicKey, privateKey);
    }
    public bool is_CreateRawRsaKeyringInput { get { return true; } }
    public Dafny.ISequence<char> dtor_keyNamespace {
      get {
        return this.keyNamespace;
      }
    }
    public Dafny.ISequence<char> dtor_keyName {
      get {
        return this.keyName;
      }
    }
    public Dafny.Aws.Crypto.PaddingScheme dtor_paddingScheme {
      get {
        return this.paddingScheme;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_publicKey {
      get {
        return this.publicKey;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_privateKey {
      get {
        return this.privateKey;
      }
    }
  }

  public class CreateDefaultCryptographicMaterialsManagerInput {
    public readonly Dafny.Aws.Crypto.IKeyring keyring;
    public CreateDefaultCryptographicMaterialsManagerInput(Dafny.Aws.Crypto.IKeyring keyring) {
      this.keyring = keyring;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput;
      return oth != null && this.keyring == oth.keyring;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyring));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateDefaultCryptographicMaterialsManagerInput.CreateDefaultCryptographicMaterialsManagerInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyring);
      s += ")";
      return s;
    }
    private static readonly CreateDefaultCryptographicMaterialsManagerInput theDefault = create(default(Dafny.Aws.Crypto.IKeyring));
    public static CreateDefaultCryptographicMaterialsManagerInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput>(Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateDefaultCryptographicMaterialsManagerInput create(Dafny.Aws.Crypto.IKeyring keyring) {
      return new CreateDefaultCryptographicMaterialsManagerInput(keyring);
    }
    public bool is_CreateDefaultCryptographicMaterialsManagerInput { get { return true; } }
    public Dafny.Aws.Crypto.IKeyring dtor_keyring {
      get {
        return this.keyring;
      }
    }
  }

  public class CreateCachingCryptographicMaterialsManagerInput {
    public readonly Dafny.Aws.Crypto.ICryptoMaterialsCache cache;
    public readonly int cacheLimitTtl;
    public readonly Dafny.Aws.Crypto.IKeyring keyring;
    public readonly Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<char>> partitionId;
    public readonly Wrappers_Compile.Option<long> limitBytes;
    public readonly Wrappers_Compile.Option<long> limitMessages;
    public CreateCachingCryptographicMaterialsManagerInput(Dafny.Aws.Crypto.ICryptoMaterialsCache cache, int cacheLimitTtl, Dafny.Aws.Crypto.IKeyring keyring, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager, Wrappers_Compile.Option<Dafny.ISequence<char>> partitionId, Wrappers_Compile.Option<long> limitBytes, Wrappers_Compile.Option<long> limitMessages) {
      this.cache = cache;
      this.cacheLimitTtl = cacheLimitTtl;
      this.keyring = keyring;
      this.materialsManager = materialsManager;
      this.partitionId = partitionId;
      this.limitBytes = limitBytes;
      this.limitMessages = limitMessages;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput;
      return oth != null && this.cache == oth.cache && this.cacheLimitTtl == oth.cacheLimitTtl && this.keyring == oth.keyring && this.materialsManager == oth.materialsManager && object.Equals(this.partitionId, oth.partitionId) && object.Equals(this.limitBytes, oth.limitBytes) && object.Equals(this.limitMessages, oth.limitMessages);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cache));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cacheLimitTtl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyring));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materialsManager));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.partitionId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.limitBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.limitMessages));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateCachingCryptographicMaterialsManagerInput.CreateCachingCryptographicMaterialsManagerInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.cache);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cacheLimitTtl);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyring);
      s += ", ";
      s += Dafny.Helpers.ToString(this.materialsManager);
      s += ", ";
      s += Dafny.Helpers.ToString(this.partitionId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.limitBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this.limitMessages);
      s += ")";
      return s;
    }
    private static readonly CreateCachingCryptographicMaterialsManagerInput theDefault = create(default(Dafny.Aws.Crypto.ICryptoMaterialsCache), 0, (Dafny.Aws.Crypto.IKeyring)null, (Dafny.Aws.Crypto.ICryptographicMaterialsManager)null, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<long>.Default(), Wrappers_Compile.Option<long>.Default());
    public static CreateCachingCryptographicMaterialsManagerInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput>(Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateCachingCryptographicMaterialsManagerInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateCachingCryptographicMaterialsManagerInput create(Dafny.Aws.Crypto.ICryptoMaterialsCache cache, int cacheLimitTtl, Dafny.Aws.Crypto.IKeyring keyring, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager, Wrappers_Compile.Option<Dafny.ISequence<char>> partitionId, Wrappers_Compile.Option<long> limitBytes, Wrappers_Compile.Option<long> limitMessages) {
      return new CreateCachingCryptographicMaterialsManagerInput(cache, cacheLimitTtl, keyring, materialsManager, partitionId, limitBytes, limitMessages);
    }
    public bool is_CreateCachingCryptographicMaterialsManagerInput { get { return true; } }
    public Dafny.Aws.Crypto.ICryptoMaterialsCache dtor_cache {
      get {
        return this.cache;
      }
    }
    public int dtor_cacheLimitTtl {
      get {
        return this.cacheLimitTtl;
      }
    }
    public Dafny.Aws.Crypto.IKeyring dtor_keyring {
      get {
        return this.keyring;
      }
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager dtor_materialsManager {
      get {
        return this.materialsManager;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<char>> dtor_partitionId {
      get {
        return this.partitionId;
      }
    }
    public Wrappers_Compile.Option<long> dtor_limitBytes {
      get {
        return this.limitBytes;
      }
    }
    public Wrappers_Compile.Option<long> dtor_limitMessages {
      get {
        return this.limitMessages;
      }
    }
  }

  public class CreateLocalCryptoMaterialsCacheInput {
    public readonly int entryCapacity;
    public readonly Wrappers_Compile.Option<int> entryPruningTailSize;
    public CreateLocalCryptoMaterialsCacheInput(int entryCapacity, Wrappers_Compile.Option<int> entryPruningTailSize) {
      this.entryCapacity = entryCapacity;
      this.entryPruningTailSize = entryPruningTailSize;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput;
      return oth != null && this.entryCapacity == oth.entryCapacity && object.Equals(this.entryPruningTailSize, oth.entryPruningTailSize);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.entryCapacity));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.entryPruningTailSize));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Crypto_Compile.CreateLocalCryptoMaterialsCacheInput.CreateLocalCryptoMaterialsCacheInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.entryCapacity);
      s += ", ";
      s += Dafny.Helpers.ToString(this.entryPruningTailSize);
      s += ")";
      return s;
    }
    private static readonly CreateLocalCryptoMaterialsCacheInput theDefault = create(0, Wrappers_Compile.Option<int>.Default());
    public static CreateLocalCryptoMaterialsCacheInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput>(Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Crypto.CreateLocalCryptoMaterialsCacheInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static CreateLocalCryptoMaterialsCacheInput create(int entryCapacity, Wrappers_Compile.Option<int> entryPruningTailSize) {
      return new CreateLocalCryptoMaterialsCacheInput(entryCapacity, entryPruningTailSize);
    }
    public bool is_CreateLocalCryptoMaterialsCacheInput { get { return true; } }
    public int dtor_entryCapacity {
      get {
        return this.entryCapacity;
      }
    }
    public Wrappers_Compile.Option<int> dtor_entryPruningTailSize {
      get {
        return this.entryPruningTailSize;
      }
    }
  }

  public interface IAwsCryptographicMaterialsProviderClient {
    Dafny.Aws.Crypto.IKeyring CreateRawAesKeyring(Dafny.Aws.Crypto.CreateRawAesKeyringInput input);
    Dafny.Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input);
  }
  public class _Companion_IAwsCryptographicMaterialsProviderClient {
  }

} // end of namespace Dafny.Aws.Crypto
namespace Dafny.Aws.Esdk {




  public class EncryptInput {
    public readonly Dafny.ISequence<byte> plaintext;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager;
    public readonly Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId;
    public EncryptInput(Dafny.ISequence<byte> plaintext, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager, Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId) {
      this.plaintext = plaintext;
      this.encryptionContext = encryptionContext;
      this.materialsManager = materialsManager;
      this.algorithmSuiteId = algorithmSuiteId;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Esdk.EncryptInput;
      return oth != null && object.Equals(this.plaintext, oth.plaintext) && object.Equals(this.encryptionContext, oth.encryptionContext) && this.materialsManager == oth.materialsManager && object.Equals(this.algorithmSuiteId, oth.algorithmSuiteId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materialsManager));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Esdk_Compile.EncryptInput.EncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.materialsManager);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteId);
      s += ")";
      return s;
    }
    private static readonly EncryptInput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, default(Dafny.Aws.Crypto.ICryptographicMaterialsManager), Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.Default());
    public static EncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptInput>(Dafny.Aws.Esdk.EncryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptInput create(Dafny.ISequence<byte> plaintext, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager, Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> algorithmSuiteId) {
      return new EncryptInput(plaintext, encryptionContext, materialsManager, algorithmSuiteId);
    }
    public bool is_EncryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager dtor_materialsManager {
      get {
        return this.materialsManager;
      }
    }
    public Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> dtor_algorithmSuiteId {
      get {
        return this.algorithmSuiteId;
      }
    }
  }

  public class EncryptOutput {
    public readonly Dafny.ISequence<byte> ciphertext;
    public EncryptOutput(Dafny.ISequence<byte> ciphertext) {
      this.ciphertext = ciphertext;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Esdk.EncryptOutput;
      return oth != null && object.Equals(this.ciphertext, oth.ciphertext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Esdk_Compile.EncryptOutput.EncryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.ciphertext);
      s += ")";
      return s;
    }
    private static readonly EncryptOutput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static EncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptOutput>(Dafny.Aws.Esdk.EncryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Esdk.EncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptOutput create(Dafny.ISequence<byte> ciphertext) {
      return new EncryptOutput(ciphertext);
    }
    public bool is_EncryptOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
  }

  public class DecryptInput {
    public readonly Dafny.ISequence<byte> ciphertext;
    public readonly Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager;
    public DecryptInput(Dafny.ISequence<byte> ciphertext, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager) {
      this.ciphertext = ciphertext;
      this.materialsManager = materialsManager;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Esdk.DecryptInput;
      return oth != null && object.Equals(this.ciphertext, oth.ciphertext) && this.materialsManager == oth.materialsManager;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.materialsManager));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Esdk_Compile.DecryptInput.DecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this.ciphertext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.materialsManager);
      s += ")";
      return s;
    }
    private static readonly DecryptInput theDefault = create(Dafny.Sequence<byte>.Empty, default(Dafny.Aws.Crypto.ICryptographicMaterialsManager));
    public static DecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptInput>(Dafny.Aws.Esdk.DecryptInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptInput create(Dafny.ISequence<byte> ciphertext, Dafny.Aws.Crypto.ICryptographicMaterialsManager materialsManager) {
      return new DecryptInput(ciphertext, materialsManager);
    }
    public bool is_DecryptInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager dtor_materialsManager {
      get {
        return this.materialsManager;
      }
    }
  }

  public class DecryptOutput {
    public readonly Dafny.ISequence<byte> plaintext;
    public DecryptOutput(Dafny.ISequence<byte> plaintext) {
      this.plaintext = plaintext;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Aws.Esdk.DecryptOutput;
      return oth != null && object.Equals(this.plaintext, oth.plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Aws.Esdk_Compile.DecryptOutput.DecryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ")";
      return s;
    }
    private static readonly DecryptOutput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static DecryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptOutput>(Dafny.Aws.Esdk.DecryptOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Aws.Esdk.DecryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptOutput create(Dafny.ISequence<byte> plaintext) {
      return new DecryptOutput(plaintext);
    }
    public bool is_DecryptOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
  }

  public interface IAwsEncryptionSdkClient {
    Wrappers_Compile.Result<Dafny.Aws.Esdk.EncryptOutput, Dafny.ISequence<char>> Encrypt(Dafny.Aws.Esdk.EncryptInput input);
    Wrappers_Compile.Result<Dafny.Aws.Esdk.DecryptOutput, Dafny.ISequence<char>> Decrypt(Dafny.Aws.Esdk.DecryptInput input);
  }
  public class _Companion_IAwsEncryptionSdkClient {
  }

} // end of namespace Dafny.Aws.Esdk
namespace Dafny.Aws {



} // end of namespace Dafny.Aws
namespace Math_Compile {

  public partial class __default {
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
  }
} // end of namespace Math_Compile
namespace Seq_Compile {



  public partial class __default {
    public static __T First<__T>(Dafny.ISequence<__T> s) {
      return (s).Select(BigInteger.Zero);
    }
    public static Dafny.ISequence<__T> DropFirst<__T>(Dafny.ISequence<__T> s) {
      return (s).Drop(BigInteger.One);
    }
    public static __T Last<__T>(Dafny.ISequence<__T> s) {
      return (s).Select((new BigInteger((s).Count)) - (BigInteger.One));
    }
    public static Dafny.ISequence<__T> DropLast<__T>(Dafny.ISequence<__T> s) {
      return (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
    }
    public static __T[] ToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      __T[] _nw4 = new __T[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      Func<BigInteger, __T> _arrayinit1 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_14132_s) => ((System.Func<BigInteger, __T>)((_14133_i) => {
        return (_14132_s).Select(_14133_i);
      })))(s);
      for (var _arrayinit_01 = 0; _arrayinit_01 < new BigInteger(_nw4.Length); _arrayinit_01++) {
        _nw4[(int)(_arrayinit_01)] = _arrayinit1(_arrayinit_01);
      }
      a = _nw4;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_14134_s) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_14134_s).Elements) {
          __T _14135_x = (__T)_compr_0;
          if ((_14134_s).Contains((_14135_x))) {
            _coll0.Add(_14135_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(s);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> s, __T v)
    {
      BigInteger _14136___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((s).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_14136___accumulator);
      } else {
        _14136___accumulator = (_14136___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in11 = (s).Drop(BigInteger.One);
        __T _in12 = v;
        s = _in11;
        v = _in12;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile.Option<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> s, __T v)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return @Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((s).Select(BigInteger.Zero), v)) {
        return @Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Wrappers_Compile.Option<BigInteger> _14137_o_k = Seq_Compile.__default.IndexOfOption<__T>((s).Drop(BigInteger.One), v);
        if ((_14137_o_k).is_Some) {
          return @Wrappers_Compile.Option<BigInteger>.create_Some(((_14137_o_k).dtor_value) + (BigInteger.One));
        } else {
          return @Wrappers_Compile.Option<BigInteger>.create_None();
        }
      }
    }
    public static BigInteger LastIndexOf<__T>(Dafny.ISequence<__T> s, __T v)
    {
    TAIL_CALL_START: ;
      if (object.Equals((s).Select((new BigInteger((s).Count)) - (BigInteger.One)), v)) {
        return (new BigInteger((s).Count)) - (BigInteger.One);
      } else {
        Dafny.ISequence<__T> _in13 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        __T _in14 = v;
        s = _in13;
        v = _in14;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile.Option<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> s, __T v)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return @Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((s).Select((new BigInteger((s).Count)) - (BigInteger.One)), v)) {
        return @Wrappers_Compile.Option<BigInteger>.create_Some((new BigInteger((s).Count)) - (BigInteger.One));
      } else {
        Dafny.ISequence<__T> _in15 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        __T _in16 = v;
        s = _in15;
        v = _in16;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Remove<__T>(Dafny.ISequence<__T> s, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat((s).Take(pos), (s).Drop((pos) + (BigInteger.One)));
    }
    public static Dafny.ISequence<__T> RemoveValue<__T>(Dafny.ISequence<__T> s, __T v)
    {
      if (!(s).Contains((v))) {
        return s;
      } else {
        BigInteger _14138_i = Seq_Compile.__default.IndexOf<__T>(s, v);
        return Dafny.Sequence<__T>.Concat((s).Take(_14138_i), (s).Drop((_14138_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> s, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((s).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (s).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> s) {
      Dafny.ISequence<__T> _14139___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((s).Equals((Dafny.Sequence<__T>.FromElements()))) {
        return Dafny.Sequence<__T>.Concat(_14139___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _14139___accumulator = Dafny.Sequence<__T>.Concat(_14139___accumulator, Dafny.Sequence<__T>.FromElements((s).Select((new BigInteger((s).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in17 = (s).Subsequence(BigInteger.Zero, (new BigInteger((s).Count)) - (BigInteger.One));
        s = _in17;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _14140___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_14140___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _14140___accumulator = Dafny.Sequence<__T>.Concat(_14140___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in18 = v;
        BigInteger _in19 = (length) - (BigInteger.One);
        v = _in18;
        length = _in19;
        goto TAIL_CALL_START;
      }
    }
    public static _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System.Tuple2<__A, __B>> s) {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return @_System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Seq_Compile.__default.Unzip<__A, __B>(Seq_Compile.__default.DropLast<_System.Tuple2<__A, __B>>(s));
        Dafny.ISequence<__A> _14141_a = ((_System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>)_let_tmp_rhs0)._0;
        Dafny.ISequence<__B> _14142_b = ((_System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>)_let_tmp_rhs0)._1;
        return @_System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_14141_a, Dafny.Sequence<__A>.FromElements((Seq_Compile.__default.Last<_System.Tuple2<__A, __B>>(s)).dtor__0)), Dafny.Sequence<__B>.Concat(_14142_b, Dafny.Sequence<__B>.FromElements((Seq_Compile.__default.Last<_System.Tuple2<__A, __B>>(s)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System.Tuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> a, Dafny.ISequence<__B> b)
    {
      Dafny.ISequence<_System.Tuple2<__A, __B>> _14143___accumulator = Dafny.Sequence<_System.Tuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((a).Count)).Sign == 0) {
        return Dafny.Sequence<_System.Tuple2<__A, __B>>.Concat(Dafny.Sequence<_System.Tuple2<__A, __B>>.FromElements(), _14143___accumulator);
      } else {
        _14143___accumulator = Dafny.Sequence<_System.Tuple2<__A, __B>>.Concat(Dafny.Sequence<_System.Tuple2<__A, __B>>.FromElements(@_System.Tuple2<__A, __B>.create(Seq_Compile.__default.Last<__A>(a), Seq_Compile.__default.Last<__B>(b))), _14143___accumulator);
        Dafny.ISequence<__A> _in20 = Seq_Compile.__default.DropLast<__A>(a);
        Dafny.ISequence<__B> _in21 = Seq_Compile.__default.DropLast<__B>(b);
        a = _in20;
        b = _in21;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Max(Dafny.ISequence<BigInteger> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return (s).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Max((s).Select(BigInteger.Zero), Seq_Compile.__default.Max((s).Drop(BigInteger.One)));
      }
    }
    public static BigInteger Min(Dafny.ISequence<BigInteger> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return (s).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Min((s).Select(BigInteger.Zero), Seq_Compile.__default.Min((s).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> s) {
      Dafny.ISequence<__T> _14144___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_14144___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _14144___accumulator = Dafny.Sequence<__T>.Concat(_14144___accumulator, (s).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in22 = (s).Drop(BigInteger.One);
        s = _in22;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> s) {
      Dafny.ISequence<__T> _14145___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _14145___accumulator);
      } else {
        _14145___accumulator = Dafny.Sequence<__T>.Concat(Seq_Compile.__default.Last<Dafny.ISequence<__T>>(s), _14145___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in23 = Seq_Compile.__default.DropLast<Dafny.ISequence<__T>>(s);
        s = _in23;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> s)
    {
      Dafny.ISequence<__R> _14146___accumulator = Dafny.Sequence<__R>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__R>.Concat(_14146___accumulator, Dafny.Sequence<__R>.FromElements());
      } else {
        _14146___accumulator = Dafny.Sequence<__R>.Concat(_14146___accumulator, Dafny.Sequence<__R>.FromElements(Dafny.Helpers.Id<Func<__T, __R>>(f)((s).Select(BigInteger.Zero))));
        Func<__T, __R> _in24 = f;
        Dafny.ISequence<__T> _in25 = (s).Drop(BigInteger.One);
        f = _in24;
        s = _in25;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Wrappers_Compile.Result<__R, __E>> f, Dafny.ISequence<__T> s)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return @Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Wrappers_Compile.Result<__R, __E> _14147_valueOrError0 = Dafny.Helpers.Id<Func<__T, Wrappers_Compile.Result<__R, __E>>>(f)((s).Select(BigInteger.Zero));
        if ((_14147_valueOrError0).IsFailure()) {
          return (_14147_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _14148_head = (_14147_valueOrError0).Extract();
          Wrappers_Compile.Result<Dafny.ISequence<__R>, __E> _14149_valueOrError1 = Seq_Compile.__default.MapWithResult<__T, __R, __E>(f, (s).Drop(BigInteger.One));
          if ((_14149_valueOrError1).IsFailure()) {
            return (_14149_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _14150_tail = (_14149_valueOrError1).Extract();
            return @Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_14148_head), _14150_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> s)
    {
      Dafny.ISequence<__T> _14151___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_14151___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _14151___accumulator = Dafny.Sequence<__T>.Concat(_14151___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in26 = f;
        Dafny.ISequence<__T> _in27 = (s).Drop(BigInteger.One);
        f = _in26;
        s = _in27;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> s)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in28 = f;
        __A _in29 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (s).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in30 = (s).Drop(BigInteger.One);
        f = _in28;
        init = _in29;
        s = _in30;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldRight<__A, __T>(Func<__T, __A, __A> f, Dafny.ISequence<__T> s, __A init)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return init;
      } else {
        return Dafny.Helpers.Id<Func<__T, __A, __A>>(f)((s).Select(BigInteger.Zero), Seq_Compile.__default.FoldRight<__A, __T>(f, (s).Drop(BigInteger.One), init));
      }
    }
  }
} // end of namespace Seq_Compile
namespace AwsKmsArnParsing_Compile {





  public class AwsResource {
    public readonly Dafny.ISequence<char> resourceType;
    public readonly Dafny.ISequence<char> @value;
    public AwsResource(Dafny.ISequence<char> resourceType, Dafny.ISequence<char> @value) {
      this.resourceType = resourceType;
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as AwsKmsArnParsing_Compile.AwsResource;
      return oth != null && object.Equals(this.resourceType, oth.resourceType) && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.resourceType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AwsKmsArnParsing_Compile.AwsResource.AwsResource";
      s += "(";
      s += Dafny.Helpers.ToString(this.resourceType);
      s += ", ";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
    private static readonly AwsResource theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static AwsResource Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource> _TYPE = new Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource>(AwsKmsArnParsing_Compile.AwsResource.Default());
    public static Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource> _TypeDescriptor() {
      return _TYPE;
    }
    public static AwsResource create(Dafny.ISequence<char> resourceType, Dafny.ISequence<char> @value) {
      return new AwsResource(resourceType, @value);
    }
    public bool is_AwsResource { get { return true; } }
    public Dafny.ISequence<char> dtor_resourceType {
      get {
        return this.resourceType;
      }
    }
    public Dafny.ISequence<char> dtor_value {
      get {
        return this.@value;
      }
    }
    public bool Valid() {
      return (true) && ((new BigInteger(((this).dtor_value).Count)).Sign == 1);
    }
    public Dafny.ISequence<char> _ToString() {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat((this).dtor_resourceType, Dafny.Sequence<char>.FromString("/")), (this).dtor_value);
    }
  }

  public class AwsArn {
    public readonly Dafny.ISequence<char> arnLiteral;
    public readonly Dafny.ISequence<char> partition;
    public readonly Dafny.ISequence<char> service;
    public readonly Dafny.ISequence<char> region;
    public readonly Dafny.ISequence<char> account;
    public readonly AwsKmsArnParsing_Compile.AwsResource resource;
    public AwsArn(Dafny.ISequence<char> arnLiteral, Dafny.ISequence<char> partition, Dafny.ISequence<char> service, Dafny.ISequence<char> region, Dafny.ISequence<char> account, AwsKmsArnParsing_Compile.AwsResource resource) {
      this.arnLiteral = arnLiteral;
      this.partition = partition;
      this.service = service;
      this.region = region;
      this.account = account;
      this.resource = resource;
    }
    public override bool Equals(object other) {
      var oth = other as AwsKmsArnParsing_Compile.AwsArn;
      return oth != null && object.Equals(this.arnLiteral, oth.arnLiteral) && object.Equals(this.partition, oth.partition) && object.Equals(this.service, oth.service) && object.Equals(this.region, oth.region) && object.Equals(this.account, oth.account) && object.Equals(this.resource, oth.resource);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.arnLiteral));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.partition));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.service));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.region));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.account));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.resource));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AwsKmsArnParsing_Compile.AwsArn.AwsArn";
      s += "(";
      s += Dafny.Helpers.ToString(this.arnLiteral);
      s += ", ";
      s += Dafny.Helpers.ToString(this.partition);
      s += ", ";
      s += Dafny.Helpers.ToString(this.service);
      s += ", ";
      s += Dafny.Helpers.ToString(this.region);
      s += ", ";
      s += Dafny.Helpers.ToString(this.account);
      s += ", ";
      s += Dafny.Helpers.ToString(this.resource);
      s += ")";
      return s;
    }
    private static readonly AwsArn theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, AwsKmsArnParsing_Compile.AwsResource.Default());
    public static AwsArn Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn> _TYPE = new Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn>(AwsKmsArnParsing_Compile.AwsArn.Default());
    public static Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn> _TypeDescriptor() {
      return _TYPE;
    }
    public static AwsArn create(Dafny.ISequence<char> arnLiteral, Dafny.ISequence<char> partition, Dafny.ISequence<char> service, Dafny.ISequence<char> region, Dafny.ISequence<char> account, AwsKmsArnParsing_Compile.AwsResource resource) {
      return new AwsArn(arnLiteral, partition, service, region, account, resource);
    }
    public bool is_AwsArn { get { return true; } }
    public Dafny.ISequence<char> dtor_arnLiteral {
      get {
        return this.arnLiteral;
      }
    }
    public Dafny.ISequence<char> dtor_partition {
      get {
        return this.partition;
      }
    }
    public Dafny.ISequence<char> dtor_service {
      get {
        return this.service;
      }
    }
    public Dafny.ISequence<char> dtor_region {
      get {
        return this.region;
      }
    }
    public Dafny.ISequence<char> dtor_account {
      get {
        return this.account;
      }
    }
    public AwsKmsArnParsing_Compile.AwsResource dtor_resource {
      get {
        return this.resource;
      }
    }
    public bool Valid() {
      return (((((((this).dtor_arnLiteral).Equals((Dafny.Sequence<char>.FromString("arn")))) && ((new BigInteger(((this).dtor_partition).Count)).Sign == 1)) && ((new BigInteger(((this).dtor_service).Count)).Sign == 1)) && ((new BigInteger(((this).dtor_region).Count)).Sign == 1)) && ((new BigInteger(((this).dtor_account).Count)).Sign == 1)) && (((this).dtor_resource).Valid());
    }
    public Dafny.ISequence<char> _ToString() {
      return (this).ToArnString(@Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None());
    }
    public Dafny.ISequence<char> ToArnString(Wrappers_Compile.Option<Dafny.ISequence<char>> customRegion) {
      var _this = this;
    TAIL_CALL_START: ;
      Wrappers_Compile.Option<Dafny.ISequence<char>> _source11 = customRegion;
      if (_source11.is_None) {
        var _in31 = _this;
        Wrappers_Compile.Option<Dafny.ISequence<char>> _in32 = @Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some((_this).dtor_region);
        _this = _in31;
        customRegion = _in32;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<char> _14152___mcc_h0 = ((Wrappers_Compile.Option_Some<Dafny.ISequence<char>>)_source11).@value;
        Dafny.ISequence<char> _14153_customRegion = _14152___mcc_h0;
        return StandardLibrary_Compile.__default.Join<char>(Dafny.Sequence<Dafny.ISequence<char>>.FromElements((_this).dtor_arnLiteral, (_this).dtor_partition, (_this).dtor_service, _14153_customRegion, (_this).dtor_account, ((_this).dtor_resource)._ToString()), Dafny.Sequence<char>.FromString(":"));
      }
    }
  }

  public partial class AwsKmsArn {
    private static readonly Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn> _TYPE = new Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn>(AwsKmsArnParsing_Compile.AwsArn.Default());
    public static Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsArn> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class AwsKmsResource {
    private static readonly Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource> _TYPE = new Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource>(AwsKmsArnParsing_Compile.AwsResource.Default());
    public static Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsResource> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public abstract class AwsKmsIdentifier {
    public AwsKmsIdentifier() { }
    private static readonly AwsKmsIdentifier theDefault = create_AwsKmsArnIdentifier(AwsKmsArnParsing_Compile.AwsArn.Default());
    public static AwsKmsIdentifier Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsKmsIdentifier> _TYPE = new Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsKmsIdentifier>(AwsKmsArnParsing_Compile.AwsKmsIdentifier.Default());
    public static Dafny.TypeDescriptor<AwsKmsArnParsing_Compile.AwsKmsIdentifier> _TypeDescriptor() {
      return _TYPE;
    }
    public static AwsKmsIdentifier create_AwsKmsArnIdentifier(AwsKmsArnParsing_Compile.AwsArn a) {
      return new AwsKmsIdentifier_AwsKmsArnIdentifier(a);
    }
    public static AwsKmsIdentifier create_AwsKmsRawResourceIdentifier(AwsKmsArnParsing_Compile.AwsResource r) {
      return new AwsKmsIdentifier_AwsKmsRawResourceIdentifier(r);
    }
    public bool is_AwsKmsArnIdentifier { get { return this is AwsKmsIdentifier_AwsKmsArnIdentifier; } }
    public bool is_AwsKmsRawResourceIdentifier { get { return this is AwsKmsIdentifier_AwsKmsRawResourceIdentifier; } }
    public AwsKmsArnParsing_Compile.AwsArn dtor_a {
      get {
        var d = this;
        return ((AwsKmsIdentifier_AwsKmsArnIdentifier)d).a; 
      }
    }
    public AwsKmsArnParsing_Compile.AwsResource dtor_r {
      get {
        var d = this;
        return ((AwsKmsIdentifier_AwsKmsRawResourceIdentifier)d).r; 
      }
    }
    public Dafny.ISequence<char> _ToString() {
      AwsKmsArnParsing_Compile.AwsKmsIdentifier _source12 = this;
      if (_source12.is_AwsKmsArnIdentifier) {
        AwsKmsArnParsing_Compile.AwsArn _14154___mcc_h0 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source12).a;
        AwsKmsArnParsing_Compile.AwsArn _14155_a = _14154___mcc_h0;
        return (_14155_a)._ToString();
      } else {
        AwsKmsArnParsing_Compile.AwsResource _14156___mcc_h1 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source12).r;
        AwsKmsArnParsing_Compile.AwsResource _14157_r = _14156___mcc_h1;
        return (_14157_r)._ToString();
      }
    }
  }
  public class AwsKmsIdentifier_AwsKmsArnIdentifier : AwsKmsIdentifier {
    public readonly AwsKmsArnParsing_Compile.AwsArn a;
    public AwsKmsIdentifier_AwsKmsArnIdentifier(AwsKmsArnParsing_Compile.AwsArn a) {
      this.a = a;
    }
    public override bool Equals(object other) {
      var oth = other as AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier;
      return oth != null && object.Equals(this.a, oth.a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.a));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AwsKmsArnParsing_Compile.AwsKmsIdentifier.AwsKmsArnIdentifier";
      s += "(";
      s += Dafny.Helpers.ToString(this.a);
      s += ")";
      return s;
    }
  }
  public class AwsKmsIdentifier_AwsKmsRawResourceIdentifier : AwsKmsIdentifier {
    public readonly AwsKmsArnParsing_Compile.AwsResource r;
    public AwsKmsIdentifier_AwsKmsRawResourceIdentifier(AwsKmsArnParsing_Compile.AwsResource r) {
      this.r = r;
    }
    public override bool Equals(object other) {
      var oth = other as AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier;
      return oth != null && object.Equals(this.r, oth.r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AwsKmsArnParsing_Compile.AwsKmsIdentifier.AwsKmsRawResourceIdentifier";
      s += "(";
      s += Dafny.Helpers.ToString(this.r);
      s += ")";
      return s;
    }
  }

  public partial class AwsKmsIdentifierString {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool ValidAwsKmsResource(AwsKmsArnParsing_Compile.AwsResource resource) {
      return ((resource).Valid()) && ((((resource).dtor_resourceType).Equals((Dafny.Sequence<char>.FromString("key")))) || (((resource).dtor_resourceType).Equals((Dafny.Sequence<char>.FromString("alias")))));
    }
    public static bool ValidAwsKmsArn(AwsKmsArnParsing_Compile.AwsArn arn) {
      return (((arn).Valid()) && (((arn).dtor_service).Equals((Dafny.Sequence<char>.FromString("kms"))))) && (AwsKmsArnParsing_Compile.__default.ValidAwsKmsResource((arn).dtor_resource));
    }
    public static Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsResource, Dafny.ISequence<char>> ParseAwsKmsRawResources(Dafny.ISequence<char> identifier) {
      Dafny.ISequence<Dafny.ISequence<char>> _14158_info = StandardLibrary_Compile.__default.Split<char>(identifier, '/');
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14159_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(!((_14158_info).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("key"))), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Malformed raw key id: "), identifier));
      if ((_14159_valueOrError0).IsFailure()) {
        return (_14159_valueOrError0).PropagateFailure<AwsKmsArnParsing_Compile.AwsResource>();
      } else if ((new BigInteger((_14158_info).Count)) == (BigInteger.One)) {
        return AwsKmsArnParsing_Compile.__default.ParseAwsKmsResources(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("key/"), identifier));
      } else {
        return AwsKmsArnParsing_Compile.__default.ParseAwsKmsResources(identifier);
      }
    }
    public static Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsResource, Dafny.ISequence<char>> ParseAwsKmsResources(Dafny.ISequence<char> identifier) {
      Dafny.ISequence<Dafny.ISequence<char>> _14160_info = StandardLibrary_Compile.__default.Split<char>(identifier, '/');
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14161_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((new BigInteger((_14160_info).Count)) > (BigInteger.One), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Malformed resource: "), identifier));
      if ((_14161_valueOrError0).IsFailure()) {
        return (_14161_valueOrError0).PropagateFailure<AwsKmsArnParsing_Compile.AwsResource>();
      } else {
        Dafny.ISequence<char> _14162_resourceType = (_14160_info).Select(BigInteger.Zero);
        Dafny.ISequence<char> _14163_value = StandardLibrary_Compile.__default.Join<char>((_14160_info).Drop(BigInteger.One), Dafny.Sequence<char>.FromString("/"));
        AwsKmsArnParsing_Compile.AwsResource _14164_resource = @AwsKmsArnParsing_Compile.AwsResource.create(_14162_resourceType, _14163_value);
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14165_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(AwsKmsArnParsing_Compile.__default.ValidAwsKmsResource(_14164_resource), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Malformed resource: "), identifier));
        if ((_14165_valueOrError1).IsFailure()) {
          return (_14165_valueOrError1).PropagateFailure<AwsKmsArnParsing_Compile.AwsResource>();
        } else {
          return @Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsResource, Dafny.ISequence<char>>.create_Success(_14164_resource);
        }
      }
    }
    public static Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsArn, Dafny.ISequence<char>> ParseAwsKmsArn(Dafny.ISequence<char> identifier) {
      Dafny.ISequence<Dafny.ISequence<char>> _14166_components = StandardLibrary_Compile.__default.Split<char>(identifier, ':');
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14167_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((new BigInteger(6)) == (new BigInteger((_14166_components).Count)), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Malformed arn: "), identifier));
      if ((_14167_valueOrError0).IsFailure()) {
        return (_14167_valueOrError0).PropagateFailure<AwsKmsArnParsing_Compile.AwsArn>();
      } else {
        Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsResource, Dafny.ISequence<char>> _14168_valueOrError1 = AwsKmsArnParsing_Compile.__default.ParseAwsKmsResources((_14166_components).Select(new BigInteger(5)));
        if ((_14168_valueOrError1).IsFailure()) {
          return (_14168_valueOrError1).PropagateFailure<AwsKmsArnParsing_Compile.AwsArn>();
        } else {
          AwsKmsArnParsing_Compile.AwsResource _14169_resource = (_14168_valueOrError1).Extract();
          AwsKmsArnParsing_Compile.AwsArn _14170_arn = @AwsKmsArnParsing_Compile.AwsArn.create((_14166_components).Select(BigInteger.Zero), (_14166_components).Select(BigInteger.One), (_14166_components).Select(new BigInteger(2)), (_14166_components).Select(new BigInteger(3)), (_14166_components).Select(new BigInteger(4)), _14169_resource);
          Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14171_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(AwsKmsArnParsing_Compile.__default.ValidAwsKmsArn(_14170_arn), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Malformed Arn:"), identifier));
          if ((_14171_valueOrError2).IsFailure()) {
            return (_14171_valueOrError2).PropagateFailure<AwsKmsArnParsing_Compile.AwsArn>();
          } else {
            return @Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsArn, Dafny.ISequence<char>>.create_Success(_14170_arn);
          }
        }
      }
    }
    public static Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>> ParseAwsKmsIdentifier(Dafny.ISequence<char> identifier) {
      if (Dafny.Sequence<char>.IsPrefixOf(Dafny.Sequence<char>.FromString("arn:"), identifier)) {
        Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsArn, Dafny.ISequence<char>> _14172_valueOrError0 = AwsKmsArnParsing_Compile.__default.ParseAwsKmsArn(identifier);
        if ((_14172_valueOrError0).IsFailure()) {
          return (_14172_valueOrError0).PropagateFailure<AwsKmsArnParsing_Compile.AwsKmsIdentifier>();
        } else {
          AwsKmsArnParsing_Compile.AwsArn _14173_arn = (_14172_valueOrError0).Extract();
          return @Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>>.create_Success(@AwsKmsArnParsing_Compile.AwsKmsIdentifier.create_AwsKmsArnIdentifier(_14173_arn));
        }
      } else {
        Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsResource, Dafny.ISequence<char>> _14174_valueOrError1 = AwsKmsArnParsing_Compile.__default.ParseAwsKmsRawResources(identifier);
        if ((_14174_valueOrError1).IsFailure()) {
          return (_14174_valueOrError1).PropagateFailure<AwsKmsArnParsing_Compile.AwsKmsIdentifier>();
        } else {
          AwsKmsArnParsing_Compile.AwsResource _14175_r = (_14174_valueOrError1).Extract();
          return @Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>>.create_Success(@AwsKmsArnParsing_Compile.AwsKmsIdentifier.create_AwsKmsRawResourceIdentifier(_14175_r));
        }
      }
    }
    public static bool IsMultiRegionAwsKmsArn(AwsKmsArnParsing_Compile.AwsArn arn) {
      return AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsResource((arn).dtor_resource);
    }
    public static bool IsMultiRegionAwsKmsIdentifier(AwsKmsArnParsing_Compile.AwsKmsIdentifier identifier) {
      AwsKmsArnParsing_Compile.AwsKmsIdentifier _source13 = identifier;
      if (_source13.is_AwsKmsArnIdentifier) {
        AwsKmsArnParsing_Compile.AwsArn _14176___mcc_h0 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source13).a;
        AwsKmsArnParsing_Compile.AwsArn _14177_arn = _14176___mcc_h0;
        return AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsArn(_14177_arn);
      } else {
        AwsKmsArnParsing_Compile.AwsResource _14178___mcc_h1 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source13).r;
        AwsKmsArnParsing_Compile.AwsResource _14179_r = _14178___mcc_h1;
        return AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsResource(_14179_r);
      }
    }
    public static bool IsMultiRegionAwsKmsResource(AwsKmsArnParsing_Compile.AwsResource resource) {
      return (((resource).dtor_resourceType).Equals((Dafny.Sequence<char>.FromString("key")))) && (Dafny.Sequence<char>.IsPrefixOf(Dafny.Sequence<char>.FromString("mrk-"), (resource).dtor_value));
    }
    public static Wrappers_Compile.Option<Dafny.ISequence<char>> GetRegion(AwsKmsArnParsing_Compile.AwsKmsIdentifier identifier) {
      AwsKmsArnParsing_Compile.AwsKmsIdentifier _source14 = identifier;
      if (_source14.is_AwsKmsArnIdentifier) {
        AwsKmsArnParsing_Compile.AwsArn _14180___mcc_h0 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source14).a;
        AwsKmsArnParsing_Compile.AwsArn _14181_a = _14180___mcc_h0;
        return @Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some((_14181_a).dtor_region);
      } else {
        AwsKmsArnParsing_Compile.AwsResource _14182___mcc_h1 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source14).r;
        return @Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None();
      }
    }
    public static BigInteger MAX__AWS__KMS__IDENTIFIER__LENGTH { get {
      return new BigInteger(2048);
    } }
  }
} // end of namespace AwsKmsArnParsing_Compile
namespace Sets {


} // end of namespace Sets
namespace EncryptionContext {








  public partial class __default {
    public static bool Serializable(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      return (EncryptionContext.__default.SerializableKVPairs(encryptionContext)) && ((EncryptionContext.__default.Length(encryptionContext)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT));
    }
    public static bool SerializableKVPairs(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      return ((new BigInteger((encryptionContext).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) && (Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, bool>>((_14183_encryptionContext) => Dafny.Helpers.Quantifier<Dafny.ISequence<byte>>(((_14183_encryptionContext).Keys).Elements, true, (((_14184_key) => {
        return !(((_14183_encryptionContext).Keys).Contains((_14184_key))) || (EncryptionContext.__default.SerializableKVPair(@_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create(_14184_key, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(_14183_encryptionContext,_14184_key))));
      }))))(encryptionContext));
    }
    public static bool SerializableKVPair(_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>> kvPair) {
      return ((((new BigInteger(((kvPair).dtor__0).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) && ((new BigInteger(((kvPair).dtor__1).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT))) && (UTF8.__default.ValidUTF8Seq((kvPair).dtor__0))) && (UTF8.__default.ValidUTF8Seq((kvPair).dtor__1));
    }
    public static BigInteger Length(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      if ((new BigInteger((encryptionContext).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        Dafny.ISequence<Dafny.ISequence<byte>> _14185_keys = StandardLibrary_Compile.__default.SetToOrderedSequence<byte>((encryptionContext).Keys, StandardLibrary_mUInt_Compile.__default.UInt8Less);
        Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14186_kvPairs = ((System.Func<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>) (() => {
          BigInteger dim1 = new BigInteger((_14185_keys).Count);
          var arr1 = new _System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>[Dafny.Helpers.ToIntChecked(dim1,"C# array size must not be larger than max 32-bit int")];
          for (int i1 = 0; i1 < dim1; i1++) {
            var _14187_i = (BigInteger) i1;
            arr1[(int)(_14187_i)] = @_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create((_14185_keys).Select(_14187_i), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(encryptionContext,(_14185_keys).Select(_14187_i)));
          }
          return Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromArray(arr1);
        }))();
        return (new BigInteger(2)) + (EncryptionContext.__default.LinearLength(_14186_kvPairs, BigInteger.Zero, new BigInteger((_14186_kvPairs).Count)));
      }
    }
    public static BigInteger LinearLength(Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> kvPairs, BigInteger lo, BigInteger hi)
    {
      if ((lo) == (hi)) {
        return BigInteger.Zero;
      } else {
        return ((((EncryptionContext.__default.LinearLength(kvPairs, lo, (hi) - (BigInteger.One))) + (new BigInteger(2))) + (new BigInteger((((kvPairs).Select((hi) - (BigInteger.One))).dtor__0).Count))) + (new BigInteger(2))) + (new BigInteger((((kvPairs).Select((hi) - (BigInteger.One))).dtor__1).Count));
      }
    }
    public static BigInteger ComputeLength(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      BigInteger res = BigInteger.Zero;
      if ((new BigInteger((encryptionContext).Count)).Sign == 0) {
        res = BigInteger.Zero;
        return res;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _14188_keys;
      Dafny.ISequence<Dafny.ISequence<byte>> _out13;
      _out13 = Sets.__default.SetToOrderedSequence<byte>((encryptionContext).Keys, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _14188_keys = _out13;
      Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14189_kvPairs;
      _14189_kvPairs = ((System.Func<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>) (() => {
        BigInteger dim2 = new BigInteger((_14188_keys).Count);
        var arr2 = new _System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>[Dafny.Helpers.ToIntChecked(dim2,"C# array size must not be larger than max 32-bit int")];
        for (int i2 = 0; i2 < dim2; i2++) {
          var _14190_i = (BigInteger) i2;
          arr2[(int)(_14190_i)] = @_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create((_14188_keys).Select(_14190_i), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(encryptionContext,(_14188_keys).Select(_14190_i)));
        }
        return Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromArray(arr2);
      }))();
      BigInteger _14191_len;
      _14191_len = new BigInteger(2);
      BigInteger _14192_i;
      _14192_i = BigInteger.Zero;
      while ((_14192_i) < (new BigInteger((_14189_kvPairs).Count))) {
        _System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>> _14193_kvPair;
        _14193_kvPair = (_14189_kvPairs).Select(_14192_i);
        _14191_len = (((_14191_len) + (new BigInteger(4))) + (new BigInteger(((_14193_kvPair).dtor__0).Count))) + (new BigInteger(((_14193_kvPair).dtor__1).Count));
        _14192_i = (_14192_i) + (BigInteger.One);
      }
      res = _14191_len;
      return res;
      return res;
    }
    public static bool CheckSerializable(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      bool res = false;
      if ((new BigInteger((encryptionContext).Count)).Sign == 0) {
        res = true;
        return res;
      } else if ((new BigInteger((encryptionContext).Count)) >= (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) {
        res = false;
        return res;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _14194_keys;
      Dafny.ISequence<Dafny.ISequence<byte>> _out14;
      _out14 = Sets.__default.SetToOrderedSequence<byte>((encryptionContext).Keys, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _14194_keys = _out14;
      Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14195_kvPairs;
      _14195_kvPairs = ((System.Func<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>) (() => {
        BigInteger dim3 = new BigInteger((_14194_keys).Count);
        var arr3 = new _System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>[Dafny.Helpers.ToIntChecked(dim3,"C# array size must not be larger than max 32-bit int")];
        for (int i3 = 0; i3 < dim3; i3++) {
          var _14196_i = (BigInteger) i3;
          arr3[(int)(_14196_i)] = @_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create((_14194_keys).Select(_14196_i), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(encryptionContext,(_14194_keys).Select(_14196_i)));
        }
        return Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromArray(arr3);
      }))();
      BigInteger _14197_kvPairsLen;
      _14197_kvPairsLen = new BigInteger(2);
      BigInteger _14198_i;
      _14198_i = BigInteger.Zero;
      while ((_14198_i) < (new BigInteger((_14195_kvPairs).Count))) {
        _System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>> _14199_kvPair;
        _14199_kvPair = (_14195_kvPairs).Select(_14198_i);
        _14197_kvPairsLen = (((_14197_kvPairsLen) + (new BigInteger(4))) + (new BigInteger(((_14199_kvPair).dtor__0).Count))) + (new BigInteger(((_14199_kvPair).dtor__1).Count));
        if (!(((new BigInteger(((_14199_kvPair).dtor__0).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) && ((new BigInteger(((_14199_kvPair).dtor__1).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)))) {
          res = false;
          return res;
        } else if ((_14197_kvPairsLen) >= (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) {
          res = false;
          return res;
        }
        _14198_i = (_14198_i) + (BigInteger.One);
      }
      res = true;
      return res;
      return res;
    }
  }
} // end of namespace EncryptionContext
namespace KMSUtils {









  public partial class GrantTokens {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>>(Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class GrantToken {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public class ResponseMetadata {
    public readonly Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> metadata;
    public readonly Dafny.ISequence<char> requestID;
    public ResponseMetadata(Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> metadata, Dafny.ISequence<char> requestID) {
      this.metadata = metadata;
      this.requestID = requestID;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.ResponseMetadata;
      return oth != null && object.Equals(this.metadata, oth.metadata) && object.Equals(this.requestID, oth.requestID);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.metadata));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.requestID));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.ResponseMetadata.ResponseMetadata";
      s += "(";
      s += Dafny.Helpers.ToString(this.metadata);
      s += ", ";
      s += Dafny.Helpers.ToString(this.requestID);
      s += ")";
      return s;
    }
    private static readonly ResponseMetadata theDefault = create(Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.Empty, Dafny.Sequence<char>.Empty);
    public static ResponseMetadata Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.ResponseMetadata> _TYPE = new Dafny.TypeDescriptor<KMSUtils.ResponseMetadata>(KMSUtils.ResponseMetadata.Default());
    public static Dafny.TypeDescriptor<KMSUtils.ResponseMetadata> _TypeDescriptor() {
      return _TYPE;
    }
    public static ResponseMetadata create(Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> metadata, Dafny.ISequence<char> requestID) {
      return new ResponseMetadata(metadata, requestID);
    }
    public bool is_ResponseMetadata { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> dtor_metadata {
      get {
        return this.metadata;
      }
    }
    public Dafny.ISequence<char> dtor_requestID {
      get {
        return this.requestID;
      }
    }
  }


  public class GenerateDataKeyRequest {
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Dafny.ISequence<Dafny.ISequence<char>> grantTokens;
    public readonly Dafny.ISequence<char> keyID;
    public readonly int numberOfBytes;
    public GenerateDataKeyRequest(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens, Dafny.ISequence<char> keyID, int numberOfBytes) {
      this.encryptionContext = encryptionContext;
      this.grantTokens = grantTokens;
      this.keyID = keyID;
      this.numberOfBytes = numberOfBytes;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.GenerateDataKeyRequest;
      return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens) && object.Equals(this.keyID, oth.keyID) && this.numberOfBytes == oth.numberOfBytes;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.numberOfBytes));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.GenerateDataKeyRequest.GenerateDataKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.numberOfBytes);
      s += ")";
      return s;
    }
    private static readonly GenerateDataKeyRequest theDefault = create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Dafny.Sequence<Dafny.ISequence<char>>.Empty, Dafny.Sequence<char>.Empty, 0);
    public static GenerateDataKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyRequest> _TYPE = new Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyRequest>(KMSUtils.GenerateDataKeyRequest.Default());
    public static Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static GenerateDataKeyRequest create(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens, Dafny.ISequence<char> keyID, int numberOfBytes) {
      return new GenerateDataKeyRequest(encryptionContext, grantTokens, keyID, numberOfBytes);
    }
    public bool is_GenerateDataKeyRequest { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.ISequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public int dtor_numberOfBytes {
      get {
        return this.numberOfBytes;
      }
    }
  }

  public class GenerateDataKeyResponse {
    public readonly Dafny.ISequence<byte> ciphertextBlob;
    public readonly Dafny.ISequence<char> keyID;
    public readonly Dafny.ISequence<byte> plaintext;
    public GenerateDataKeyResponse(Dafny.ISequence<byte> ciphertextBlob, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext) {
      this.ciphertextBlob = ciphertextBlob;
      this.keyID = keyID;
      this.plaintext = plaintext;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.GenerateDataKeyResponse;
      return oth != null && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.GenerateDataKeyResponse.GenerateDataKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.ciphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ")";
      return s;
    }
    private static readonly GenerateDataKeyResponse theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty);
    public static GenerateDataKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyResponse> _TYPE = new Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyResponse>(KMSUtils.GenerateDataKeyResponse.Default());
    public static Dafny.TypeDescriptor<KMSUtils.GenerateDataKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static GenerateDataKeyResponse create(Dafny.ISequence<byte> ciphertextBlob, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext) {
      return new GenerateDataKeyResponse(ciphertextBlob, keyID, plaintext);
    }
    public bool is_GenerateDataKeyResponse { get { return true; } }
    public Dafny.ISequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public Dafny.ISequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public bool IsWellFormed() {
      return ((new BigInteger(((this).dtor_keyID).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) && ((new BigInteger(((this).dtor_ciphertextBlob).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT));
    }
  }

  public class EncryptRequest {
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Dafny.ISequence<Dafny.ISequence<char>> grantTokens;
    public readonly Dafny.ISequence<char> keyID;
    public readonly Dafny.ISequence<byte> plaintext;
    public EncryptRequest(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext) {
      this.encryptionContext = encryptionContext;
      this.grantTokens = grantTokens;
      this.keyID = keyID;
      this.plaintext = plaintext;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.EncryptRequest;
      return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens) && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.EncryptRequest.EncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ")";
      return s;
    }
    private static readonly EncryptRequest theDefault = create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Dafny.Sequence<Dafny.ISequence<char>>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty);
    public static EncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.EncryptRequest> _TYPE = new Dafny.TypeDescriptor<KMSUtils.EncryptRequest>(KMSUtils.EncryptRequest.Default());
    public static Dafny.TypeDescriptor<KMSUtils.EncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptRequest create(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext) {
      return new EncryptRequest(encryptionContext, grantTokens, keyID, plaintext);
    }
    public bool is_EncryptRequest { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.ISequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
  }

  public class EncryptResponse {
    public readonly Dafny.ISequence<byte> ciphertextBlob;
    public readonly BigInteger contentLength;
    public readonly BigInteger httpStatusCode;
    public readonly Dafny.ISequence<char> keyID;
    public readonly KMSUtils.ResponseMetadata responseMetadata;
    public EncryptResponse(Dafny.ISequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.ISequence<char> keyID, KMSUtils.ResponseMetadata responseMetadata) {
      this.ciphertextBlob = ciphertextBlob;
      this.contentLength = contentLength;
      this.httpStatusCode = httpStatusCode;
      this.keyID = keyID;
      this.responseMetadata = responseMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.EncryptResponse;
      return oth != null && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && this.contentLength == oth.contentLength && this.httpStatusCode == oth.httpStatusCode && object.Equals(this.keyID, oth.keyID) && object.Equals(this.responseMetadata, oth.responseMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.httpStatusCode));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.responseMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.EncryptResponse.EncryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.ciphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.contentLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.httpStatusCode);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.responseMetadata);
      s += ")";
      return s;
    }
    private static readonly EncryptResponse theDefault = create(Dafny.Sequence<byte>.Empty, BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<char>.Empty, KMSUtils.ResponseMetadata.Default());
    public static EncryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.EncryptResponse> _TYPE = new Dafny.TypeDescriptor<KMSUtils.EncryptResponse>(KMSUtils.EncryptResponse.Default());
    public static Dafny.TypeDescriptor<KMSUtils.EncryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptResponse create(Dafny.ISequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.ISequence<char> keyID, KMSUtils.ResponseMetadata responseMetadata) {
      return new EncryptResponse(ciphertextBlob, contentLength, httpStatusCode, keyID, responseMetadata);
    }
    public bool is_EncryptResponse { get { return true; } }
    public Dafny.ISequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public BigInteger dtor_contentLength {
      get {
        return this.contentLength;
      }
    }
    public BigInteger dtor_httpStatusCode {
      get {
        return this.httpStatusCode;
      }
    }
    public Dafny.ISequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public KMSUtils.ResponseMetadata dtor_responseMetadata {
      get {
        return this.responseMetadata;
      }
    }
    public bool IsWellFormed() {
      return ((new BigInteger(((this).dtor_keyID).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) && ((new BigInteger(((this).dtor_ciphertextBlob).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT));
    }
  }

  public class DecryptRequest {
    public readonly Dafny.ISequence<char> keyId;
    public readonly Dafny.ISequence<byte> ciphertextBlob;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Dafny.ISequence<Dafny.ISequence<char>> grantTokens;
    public DecryptRequest(Dafny.ISequence<char> keyId, Dafny.ISequence<byte> ciphertextBlob, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens) {
      this.keyId = keyId;
      this.ciphertextBlob = ciphertextBlob;
      this.encryptionContext = encryptionContext;
      this.grantTokens = grantTokens;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.DecryptRequest;
      return oth != null && object.Equals(this.keyId, oth.keyId) && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.DecryptRequest.DecryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.keyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ciphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.grantTokens);
      s += ")";
      return s;
    }
    private static readonly DecryptRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static DecryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.DecryptRequest> _TYPE = new Dafny.TypeDescriptor<KMSUtils.DecryptRequest>(KMSUtils.DecryptRequest.Default());
    public static Dafny.TypeDescriptor<KMSUtils.DecryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptRequest create(Dafny.ISequence<char> keyId, Dafny.ISequence<byte> ciphertextBlob, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<Dafny.ISequence<char>> grantTokens) {
      return new DecryptRequest(keyId, ciphertextBlob, encryptionContext, grantTokens);
    }
    public bool is_DecryptRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this.keyId;
      }
    }
    public Dafny.ISequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
  }

  public class DecryptResponse {
    public readonly BigInteger contentLength;
    public readonly BigInteger httpStatusCode;
    public readonly Dafny.ISequence<char> keyID;
    public readonly Dafny.ISequence<byte> plaintext;
    public readonly KMSUtils.ResponseMetadata responseMetadata;
    public DecryptResponse(BigInteger contentLength, BigInteger httpStatusCode, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      this.contentLength = contentLength;
      this.httpStatusCode = httpStatusCode;
      this.keyID = keyID;
      this.plaintext = plaintext;
      this.responseMetadata = responseMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.DecryptResponse;
      return oth != null && this.contentLength == oth.contentLength && this.httpStatusCode == oth.httpStatusCode && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext) && object.Equals(this.responseMetadata, oth.responseMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.httpStatusCode));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.responseMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.DecryptResponse.DecryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this.contentLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.httpStatusCode);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.responseMetadata);
      s += ")";
      return s;
    }
    private static readonly DecryptResponse theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, KMSUtils.ResponseMetadata.Default());
    public static DecryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KMSUtils.DecryptResponse> _TYPE = new Dafny.TypeDescriptor<KMSUtils.DecryptResponse>(KMSUtils.DecryptResponse.Default());
    public static Dafny.TypeDescriptor<KMSUtils.DecryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptResponse create(BigInteger contentLength, BigInteger httpStatusCode, Dafny.ISequence<char> keyID, Dafny.ISequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      return new DecryptResponse(contentLength, httpStatusCode, keyID, plaintext, responseMetadata);
    }
    public bool is_DecryptResponse { get { return true; } }
    public BigInteger dtor_contentLength {
      get {
        return this.contentLength;
      }
    }
    public BigInteger dtor_httpStatusCode {
      get {
        return this.httpStatusCode;
      }
    }
    public Dafny.ISequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public KMSUtils.ResponseMetadata dtor_responseMetadata {
      get {
        return this.responseMetadata;
      }
    }
  }

  public interface DafnyAWSKMSClientSupplier {
    Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>> GetClient(Wrappers_Compile.Option<Dafny.ISequence<char>> region);
  }
  public class _Companion_DafnyAWSKMSClientSupplier {
  }

  public partial class BaseClientSupplier : KMSUtils.DafnyAWSKMSClientSupplier {
    public BaseClientSupplier() {
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>> GetClient(Wrappers_Compile.Option<Dafny.ISequence<char>> region)
    {
      Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>> res = default(Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>>);
      Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>> _14200_resClient;
      Wrappers_Compile.Result<Amazon.KeyManagementService.IAmazonKeyManagementService, Dafny.ISequence<char>> _out15;
      _out15 = KMSUtils.ClientHelper.GetDefaultAWSKMSServiceClientExtern(region);
      _14200_resClient = _out15;
      res = _14200_resClient;
      return res;
      return res;
    }
  }

  public partial class __default {
    public static BigInteger MAX__GRANT__TOKENS { get {
      return new BigInteger(10);
    } }
  }
} // end of namespace KMSUtils
namespace AlgorithmSuite {







  public partial class ID {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    public static readonly ushort Witness = (ushort)(20);
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(AlgorithmSuite.ID.Witness);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionSuites.EncryptionSuite EncryptionSuite(ushort _this) {
      return (Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm;
    }
    public static BigInteger KeyLength(ushort _this) {
      return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_keyLen);
    }
    public static bool ContainsIdentityKDF(ushort _this) {
      return object.Equals((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_hkdf, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY());
    }
    public static BigInteger KDFInputKeyLength(ushort _this) {
      KeyDerivationAlgorithms.KeyDerivationAlgorithm _source15 = (Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_hkdf;
      if (_source15.is_HKDF__WITH__SHA__384) {
        return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_keyLen);
      } else if (_source15.is_HKDF__WITH__SHA__256) {
        return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_keyLen);
      } else {
        return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_keyLen);
      }
    }
    public static BigInteger IVLength(ushort _this) {
      return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_ivLen);
    }
    public static BigInteger TagLength(ushort _this) {
      return new BigInteger(((Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_algorithm).dtor_tagLen);
    }
    public static Wrappers_Compile.Option<Signature.ECDSAParams> SignatureType(ushort _this) {
      return (Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,_this)).dtor_sign;
    }
    public static bool ValidPlaintextDataKey(ushort _this, Dafny.ISequence<byte> plaintextDataKey) {
      return (new BigInteger((plaintextDataKey).Count)) == (AlgorithmSuite.ID.KDFInputKeyLength(_this));
    }
  }

  public class AlgSuite {
    public readonly EncryptionSuites.EncryptionSuite algorithm;
    public readonly KeyDerivationAlgorithms.KeyDerivationAlgorithm hkdf;
    public readonly Wrappers_Compile.Option<Signature.ECDSAParams> sign;
    public AlgSuite(EncryptionSuites.EncryptionSuite algorithm, KeyDerivationAlgorithms.KeyDerivationAlgorithm hkdf, Wrappers_Compile.Option<Signature.ECDSAParams> sign) {
      this.algorithm = algorithm;
      this.hkdf = hkdf;
      this.sign = sign;
    }
    public override bool Equals(object other) {
      var oth = other as AlgorithmSuite.AlgSuite;
      return oth != null && object.Equals(this.algorithm, oth.algorithm) && object.Equals(this.hkdf, oth.hkdf) && object.Equals(this.sign, oth.sign);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.hkdf));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.sign));
      return (int) hash;
    }
    public override string ToString() {
      string s = "AlgorithmSuite_Compile.AlgSuite.AlgSuite";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.hkdf);
      s += ", ";
      s += Dafny.Helpers.ToString(this.sign);
      s += ")";
      return s;
    }
    private static readonly AlgSuite theDefault = create(EncryptionSuites.EncryptionSuite.Default(), KeyDerivationAlgorithms.KeyDerivationAlgorithm.Default(), Wrappers_Compile.Option<Signature.ECDSAParams>.Default());
    public static AlgSuite Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AlgorithmSuite.AlgSuite> _TYPE = new Dafny.TypeDescriptor<AlgorithmSuite.AlgSuite>(AlgorithmSuite.AlgSuite.Default());
    public static Dafny.TypeDescriptor<AlgorithmSuite.AlgSuite> _TypeDescriptor() {
      return _TYPE;
    }
    public static AlgSuite create(EncryptionSuites.EncryptionSuite algorithm, KeyDerivationAlgorithms.KeyDerivationAlgorithm hkdf, Wrappers_Compile.Option<Signature.ECDSAParams> sign) {
      return new AlgSuite(algorithm, hkdf, sign);
    }
    public bool is_AlgSuite { get { return true; } }
    public EncryptionSuites.EncryptionSuite dtor_algorithm {
      get {
        return this.algorithm;
      }
    }
    public KeyDerivationAlgorithms.KeyDerivationAlgorithm dtor_hkdf {
      get {
        return this.hkdf;
      }
    }
    public Wrappers_Compile.Option<Signature.ECDSAParams> dtor_sign {
      get {
        return this.sign;
      }
    }
  }

  public partial class __default {
    public static ushort PolymorphIDToInternalID(Dafny.Aws.Crypto.AlgorithmSuiteId input) {
      if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF())) {
        return AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF())) {
        return AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF())) {
        return AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256())) {
        return AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256())) {
        return AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256())) {
        return AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256())) {
        return AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256;
      } else if (object.Equals(input, @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384())) {
        return AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384;
      } else {
        return AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384;
      }
    }
    public static Dafny.Aws.Crypto.AlgorithmSuiteId InternalIDToPolymorphID(ushort input) {
      if ((input) == (AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF();
      } else if ((input) == (AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF();
      } else if ((input) == (AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF();
      } else if ((input) == (AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256();
      } else if ((input) == (AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256();
      } else if ((input) == (AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256();
      } else if ((input) == (AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256();
      } else if ((input) == (AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384)) {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
      } else {
        return @Dafny.Aws.Crypto.AlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384();
      }
    }
    public static Dafny.ISet<ushort> VALID__IDS { get {
      return Dafny.Set<ushort>.FromElements(888, 838, 532, 376, 326, 276, 120, 70, 20);
    } }
    public static ushort AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get {
      return 888;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get {
      return 838;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256 { get {
      return 532;
    } }
    public static ushort AES__256__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG { get {
      return 376;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG { get {
      return 326;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG { get {
      return 276;
    } }
    public static ushort AES__256__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG { get {
      return 120;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG { get {
      return 70;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG { get {
      return 20;
    } }
    public static Dafny.IMap<ushort,AlgorithmSuite.AlgSuite> Suite { get {
      return Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.FromElements(new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__384(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P384()))), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__384(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P384()))), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__256(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P256()))), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__256(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__256(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_HKDF__WITH__SHA__256(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__192__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,AlgorithmSuite.AlgSuite>(AlgorithmSuite.__default.AES__128__GCM__IV12__TAG16__IDENTITY__NO__SIGNATURE__ALG,@AlgorithmSuite.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY(), @Wrappers_Compile.Option<Signature.ECDSAParams>.create_None())));
    } }
  }
} // end of namespace AlgorithmSuite
namespace Materials {







  public class EncryptedDataKey {
    public readonly Dafny.ISequence<byte> providerID;
    public readonly Dafny.ISequence<byte> providerInfo;
    public readonly Dafny.ISequence<byte> ciphertext;
    public EncryptedDataKey(Dafny.ISequence<byte> providerID, Dafny.ISequence<byte> providerInfo, Dafny.ISequence<byte> ciphertext) {
      this.providerID = providerID;
      this.providerInfo = providerInfo;
      this.ciphertext = ciphertext;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.EncryptedDataKey;
      return oth != null && object.Equals(this.providerID, oth.providerID) && object.Equals(this.providerInfo, oth.providerInfo) && object.Equals(this.ciphertext, oth.ciphertext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.providerID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.providerInfo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.EncryptedDataKey.EncryptedDataKey";
      s += "(";
      s += Dafny.Helpers.ToString(this.providerID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.providerInfo);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ciphertext);
      s += ")";
      return s;
    }
    private static readonly EncryptedDataKey theDefault = create(UTF8.ValidUTF8Bytes.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static EncryptedDataKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Materials.EncryptedDataKey> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptedDataKey>(Materials.EncryptedDataKey.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptedDataKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptedDataKey create(Dafny.ISequence<byte> providerID, Dafny.ISequence<byte> providerInfo, Dafny.ISequence<byte> ciphertext) {
      return new EncryptedDataKey(providerID, providerInfo, ciphertext);
    }
    public bool is_EncryptedDataKey { get { return true; } }
    public Dafny.ISequence<byte> dtor_providerID {
      get {
        return this.providerID;
      }
    }
    public Dafny.ISequence<byte> dtor_providerInfo {
      get {
        return this.providerInfo;
      }
    }
    public Dafny.ISequence<byte> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
    public static Materials.EncryptedDataKey ValidWitness() {
      return @Materials.EncryptedDataKey.create(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements());
    }
  }

  public partial class ValidEncryptedDataKey {
    private static readonly Materials.EncryptedDataKey Witness = Materials.EncryptedDataKey.ValidWitness();
    public static Materials.EncryptedDataKey Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Materials.EncryptedDataKey> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptedDataKey>(Materials.ValidEncryptedDataKey.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptedDataKey> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public class EncryptionMaterials {
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly ushort algorithmSuiteID;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey;
    public readonly Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey;
    public EncryptionMaterials(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, ushort algorithmSuiteID, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys, Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey) {
      this.encryptionContext = encryptionContext;
      this.algorithmSuiteID = algorithmSuiteID;
      this.plaintextDataKey = plaintextDataKey;
      this.encryptedDataKeys = encryptedDataKeys;
      this.signingKey = signingKey;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.EncryptionMaterials;
      return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.signingKey, oth.signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.EncryptionMaterials.EncryptionMaterials";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this.signingKey);
      s += ")";
      return s;
    }
    private static readonly EncryptionMaterials theDefault = create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, AlgorithmSuite.ID.Witness, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<Materials.EncryptedDataKey>.Empty, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static EncryptionMaterials Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptionMaterials>(Materials.EncryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionMaterials create(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, ushort algorithmSuiteID, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys, Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey) {
      return new EncryptionMaterials(encryptionContext, algorithmSuiteID, plaintextDataKey, encryptedDataKeys, signingKey);
    }
    public bool is_EncryptionMaterials { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Dafny.ISequence<Materials.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_signingKey {
      get {
        return this.signingKey;
      }
    }
    public static Materials.EncryptionMaterials ValidWitness() {
      return @Materials.EncryptionMaterials.create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(), @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim4 = new BigInteger(32);
  var arr4 = new byte[Dafny.Helpers.ToIntChecked(dim4,"C# array size must not be larger than max 32-bit int")];
  for (int i4 = 0; i4 < dim4; i4++) {
    var _14201_i = (BigInteger) i4;
    arr4[(int)(_14201_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr4);
}))()));
    }
    public static Materials.EncryptionMaterials WithoutDataKeys(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, ushort algorithmSuiteID, Wrappers_Compile.Option<Dafny.ISequence<byte>> signingKey)
    {
      Materials.EncryptionMaterials _14202_m = @Materials.EncryptionMaterials.create(encryptionContext, algorithmSuiteID, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(), signingKey);
      return _14202_m;
    }
    public Materials.EncryptionMaterials WithKeys(Wrappers_Compile.Option<Dafny.ISequence<byte>> newPlaintextDataKey, Dafny.ISequence<Materials.EncryptedDataKey> newEncryptedDataKeys)
    {
      Materials.EncryptionMaterials _14203_r = Dafny.Helpers.Let<Materials.EncryptionMaterials, Materials.EncryptionMaterials>(this, _pat_let1_0 => Dafny.Helpers.Let<Materials.EncryptionMaterials, Materials.EncryptionMaterials>(_pat_let1_0, _14204_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Materials.EncryptedDataKey>, Materials.EncryptionMaterials>(Dafny.Sequence<Materials.EncryptedDataKey>.Concat((this).dtor_encryptedDataKeys, newEncryptedDataKeys), _pat_let2_0 => Dafny.Helpers.Let<Dafny.ISequence<Materials.EncryptedDataKey>, Materials.EncryptionMaterials>(_pat_let2_0, _14205_dt__update_hencryptedDataKeys_h0 => Dafny.Helpers.Let<Wrappers_Compile.Option<Dafny.ISequence<byte>>, Materials.EncryptionMaterials>(newPlaintextDataKey, _pat_let3_0 => Dafny.Helpers.Let<Wrappers_Compile.Option<Dafny.ISequence<byte>>, Materials.EncryptionMaterials>(_pat_let3_0, _14206_dt__update_hplaintextDataKey_h0 => @Materials.EncryptionMaterials.create((_14204_dt__update__tmp_h0).dtor_encryptionContext, (_14204_dt__update__tmp_h0).dtor_algorithmSuiteID, _14206_dt__update_hplaintextDataKey_h0, _14205_dt__update_hencryptedDataKeys_h0, (_14204_dt__update__tmp_h0).dtor_signingKey)))))));
      return _14203_r;
    }
  }

  public partial class ValidEncryptionMaterials {
    private static readonly Materials.EncryptionMaterials Witness = Materials.EncryptionMaterials.ValidWitness();
    public static Materials.EncryptionMaterials Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptionMaterials>(Materials.ValidEncryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class EmptyEncryptionMaterials {
    private static readonly Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptionMaterials>(Materials.EncryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class UseableEncryptionMaterials {
    private static readonly Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptionMaterials>(Materials.EncryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public class DecryptionMaterials {
    public readonly ushort algorithmSuiteID;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey;
    public readonly Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey;
    public DecryptionMaterials(ushort algorithmSuiteID, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey) {
      this.algorithmSuiteID = algorithmSuiteID;
      this.encryptionContext = encryptionContext;
      this.plaintextDataKey = plaintextDataKey;
      this.verificationKey = verificationKey;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.DecryptionMaterials;
      return oth != null && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.verificationKey, oth.verificationKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.verificationKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.DecryptionMaterials.DecryptionMaterials";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this.verificationKey);
      s += ")";
      return s;
    }
    private static readonly DecryptionMaterials theDefault = create(AlgorithmSuite.ID.Witness, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static DecryptionMaterials Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterials>(Materials.DecryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptionMaterials create(ushort algorithmSuiteID, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey) {
      return new DecryptionMaterials(algorithmSuiteID, encryptionContext, plaintextDataKey, verificationKey);
    }
    public bool is_DecryptionMaterials { get { return true; } }
    public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Wrappers_Compile.Option<Dafny.ISequence<byte>> dtor_verificationKey {
      get {
        return this.verificationKey;
      }
    }
    public static Materials.DecryptionMaterials ValidWitness() {
      return @Materials.DecryptionMaterials.create(AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim5 = new BigInteger(32);
  var arr5 = new byte[Dafny.Helpers.ToIntChecked(dim5,"C# array size must not be larger than max 32-bit int")];
  for (int i5 = 0; i5 < dim5; i5++) {
    var _14207_i = (BigInteger) i5;
    arr5[(int)(_14207_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr5);
}))()), @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim6 = new BigInteger(32);
  var arr6 = new byte[Dafny.Helpers.ToIntChecked(dim6,"C# array size must not be larger than max 32-bit int")];
  for (int i6 = 0; i6 < dim6; i6++) {
    var _14208_i = (BigInteger) i6;
    arr6[(int)(_14208_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr6);
}))()));
    }
    public static Materials.DecryptionMaterials WithoutPlaintextDataKey(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, ushort algorithmSuiteID, Wrappers_Compile.Option<Dafny.ISequence<byte>> verificationKey)
    {
      Materials.DecryptionMaterials _14209_m = @Materials.DecryptionMaterials.create(algorithmSuiteID, encryptionContext, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), verificationKey);
      return _14209_m;
    }
    public Materials.DecryptionMaterials WithPlaintextDataKey(Dafny.ISequence<byte> plaintextDataKey) {
      Materials.DecryptionMaterials _14210_m = Dafny.Helpers.Let<Materials.DecryptionMaterials, Materials.DecryptionMaterials>(this, _pat_let4_0 => Dafny.Helpers.Let<Materials.DecryptionMaterials, Materials.DecryptionMaterials>(_pat_let4_0, _14211_dt__update__tmp_h0 => Dafny.Helpers.Let<Wrappers_Compile.Option<Dafny.ISequence<byte>>, Materials.DecryptionMaterials>(@Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(plaintextDataKey), _pat_let5_0 => Dafny.Helpers.Let<Wrappers_Compile.Option<Dafny.ISequence<byte>>, Materials.DecryptionMaterials>(_pat_let5_0, _14212_dt__update_hplaintextDataKey_h0 => @Materials.DecryptionMaterials.create((_14211_dt__update__tmp_h0).dtor_algorithmSuiteID, (_14211_dt__update__tmp_h0).dtor_encryptionContext, _14212_dt__update_hplaintextDataKey_h0, (_14211_dt__update__tmp_h0).dtor_verificationKey)))));
      return _14210_m;
    }
  }

  public partial class PendingDecryptionMaterials {
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterials>(Materials.DecryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class CompleteDecryptionMaterials {
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterials>(Materials.DecryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ValidDecryptionMaterials {
    private static readonly Materials.DecryptionMaterials Witness = Materials.DecryptionMaterials.ValidWitness();
    public static Materials.DecryptionMaterials Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterials>(Materials.ValidDecryptionMaterials.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterials> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public class EncryptionMaterialsRequest {
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Wrappers_Compile.Option<ushort> algorithmSuiteID;
    public readonly Wrappers_Compile.Option<BigInteger> plaintextLength;
    public EncryptionMaterialsRequest(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<ushort> algorithmSuiteID, Wrappers_Compile.Option<BigInteger> plaintextLength) {
      this.encryptionContext = encryptionContext;
      this.algorithmSuiteID = algorithmSuiteID;
      this.plaintextLength = plaintextLength;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.EncryptionMaterialsRequest;
      return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.algorithmSuiteID, oth.algorithmSuiteID) && object.Equals(this.plaintextLength, oth.plaintextLength);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.EncryptionMaterialsRequest.EncryptionMaterialsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextLength);
      s += ")";
      return s;
    }
    private static readonly EncryptionMaterialsRequest theDefault = create(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Wrappers_Compile.Option<ushort>.Default(), Wrappers_Compile.Option<BigInteger>.Default());
    public static EncryptionMaterialsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Materials.EncryptionMaterialsRequest> _TYPE = new Dafny.TypeDescriptor<Materials.EncryptionMaterialsRequest>(Materials.EncryptionMaterialsRequest.Default());
    public static Dafny.TypeDescriptor<Materials.EncryptionMaterialsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptionMaterialsRequest create(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<ushort> algorithmSuiteID, Wrappers_Compile.Option<BigInteger> plaintextLength) {
      return new EncryptionMaterialsRequest(encryptionContext, algorithmSuiteID, plaintextLength);
    }
    public bool is_EncryptionMaterialsRequest { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Wrappers_Compile.Option<ushort> dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Wrappers_Compile.Option<BigInteger> dtor_plaintextLength {
      get {
        return this.plaintextLength;
      }
    }
  }

  public class DecryptionMaterialsRequest {
    public readonly ushort algorithmSuiteID;
    public readonly Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public DecryptionMaterialsRequest(ushort algorithmSuiteID, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      this.algorithmSuiteID = algorithmSuiteID;
      this.encryptedDataKeys = encryptedDataKeys;
      this.encryptionContext = encryptionContext;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.DecryptionMaterialsRequest;
      return oth != null && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.encryptionContext, oth.encryptionContext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.DecryptionMaterialsRequest.DecryptionMaterialsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ")";
      return s;
    }
    private static readonly DecryptionMaterialsRequest theDefault = create(AlgorithmSuite.ID.Witness, Dafny.Sequence<Materials.EncryptedDataKey>.Empty, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
    public static DecryptionMaterialsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest>(Materials.DecryptionMaterialsRequest.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptionMaterialsRequest create(ushort algorithmSuiteID, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      return new DecryptionMaterialsRequest(algorithmSuiteID, encryptedDataKeys, encryptionContext);
    }
    public bool is_DecryptionMaterialsRequest { get { return true; } }
    public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.ISequence<Materials.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public static Materials.DecryptionMaterialsRequest ValidWitness() {
      return @Materials.DecryptionMaterialsRequest.create(AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(Materials.EncryptedDataKey.ValidWitness()), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements());
    }
  }

  public partial class ValidDecryptionMaterialsRequest {
    private static readonly Materials.DecryptionMaterialsRequest Witness = Materials.DecryptionMaterialsRequest.ValidWitness();
    public static Materials.DecryptionMaterialsRequest Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest> _TYPE = new Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest>(Materials.ValidDecryptionMaterialsRequest.Default());
    public static Dafny.TypeDescriptor<Materials.DecryptionMaterialsRequest> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static Dafny.ISequence<byte> EC__PUBLIC__KEY__FIELD { get {
      Dafny.ISequence<byte> _14213_s = Dafny.Sequence<byte>.FromElements(97, 119, 115, 45, 99, 114, 121, 112, 116, 111, 45, 112, 117, 98, 108, 105, 99, 45, 107, 101, 121);
      return _14213_s;
    } }
    public static Dafny.ISet<Dafny.ISequence<byte>> RESERVED__KEY__VALUES { get {
      return Dafny.Set<Dafny.ISequence<byte>>.FromElements(Materials.__default.EC__PUBLIC__KEY__FIELD);
    } }
  }
} // end of namespace Materials
namespace Base64_Compile {



  public partial class index {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint24 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsBase64Char(char c) {
      return (((((c) == ('+')) || ((c) == ('/'))) || ((('0') <= (c)) && ((c) <= ('9')))) || ((('A') <= (c)) && ((c) <= ('Z')))) || ((('a') <= (c)) && ((c) <= ('z')));
    }
    public static bool IsUnpaddedBase64String(Dafny.ISequence<char> s) {
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_14214_s) => Dafny.Helpers.Quantifier<char>((_14214_s).UniqueElements, true, (((_14215_k) => {
        return !((_14214_s).Contains((_14215_k))) || (Base64_Compile.__default.IsBase64Char(_14215_k));
      }))))(s));
    }
    public static char IndexToChar(byte i) {
      if ((i) == (63)) {
        return '/';
      } else if ((i) == (62)) {
        return '+';
      } else if (((52) <= (i)) && ((i) <= (61))) {
        return (char)((byte)((i) - (4)));
      } else if (((26) <= (i)) && ((i) <= (51))) {
        return (char)(((char)(i)) + ((char)(new BigInteger(71))));
      } else {
        return (char)(((char)(i)) + ((char)(new BigInteger(65))));
      }
    }
    public static byte CharToIndex(char c) {
      if ((c) == ('/')) {
        return 63;
      } else if ((c) == ('+')) {
        return 62;
      } else if ((('0') <= (c)) && ((c) <= ('9'))) {
        return (byte)((char)((c) + ((char)(new BigInteger(4)))));
      } else if ((('a') <= (c)) && ((c) <= ('z'))) {
        return (byte)((char)((c) - ((char)(new BigInteger(71)))));
      } else {
        return (byte)((char)((c) - ((char)(new BigInteger(65)))));
      }
    }
    public static Dafny.ISequence<byte> UInt24ToSeq(uint x) {
      byte _14216_b0 = (byte)((x) / (65536U));
      uint _14217_x0 = (x) - (((uint)(_14216_b0)) * (65536U));
      byte _14218_b1 = (byte)((_14217_x0) / (256U));
      byte _14219_b2 = (byte)((_14217_x0) % (256U));
      return Dafny.Sequence<byte>.FromElements(_14216_b0, _14218_b1, _14219_b2);
    }
    public static uint SeqToUInt24(Dafny.ISequence<byte> s) {
      return ((((uint)((s).Select(BigInteger.Zero))) * (65536U)) + (((uint)((s).Select(BigInteger.One))) * (256U))) + ((uint)((s).Select(new BigInteger(2))));
    }
    public static Dafny.ISequence<byte> UInt24ToIndexSeq(uint x) {
      byte _14220_b0 = (byte)((x) / (262144U));
      uint _14221_x0 = (x) - (((uint)(_14220_b0)) * (262144U));
      byte _14222_b1 = (byte)((_14221_x0) / (4096U));
      uint _14223_x1 = (_14221_x0) - (((uint)(_14222_b1)) * (4096U));
      byte _14224_b2 = (byte)((_14223_x1) / (64U));
      byte _14225_b3 = (byte)((_14223_x1) % (64U));
      return Dafny.Sequence<byte>.FromElements(_14220_b0, _14222_b1, _14224_b2, _14225_b3);
    }
    public static uint IndexSeqToUInt24(Dafny.ISequence<byte> s) {
      return (((((uint)((s).Select(BigInteger.Zero))) * (262144U)) + (((uint)((s).Select(BigInteger.One))) * (4096U))) + (((uint)((s).Select(new BigInteger(2)))) * (64U))) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> DecodeBlock(Dafny.ISequence<byte> s) {
      return Base64_Compile.__default.UInt24ToSeq(Base64_Compile.__default.IndexSeqToUInt24(s));
    }
    public static Dafny.ISequence<byte> EncodeBlock(Dafny.ISequence<byte> s) {
      return Base64_Compile.__default.UInt24ToIndexSeq(Base64_Compile.__default.SeqToUInt24(s));
    }
    public static Dafny.ISequence<byte> DecodeRecursively(Dafny.ISequence<byte> s) {
      Dafny.ISequence<byte> _14226___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_14226___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _14226___accumulator = Dafny.Sequence<byte>.Concat(_14226___accumulator, Base64_Compile.__default.DecodeBlock((s).Take(new BigInteger(4))));
        Dafny.ISequence<byte> _in33 = (s).Drop(new BigInteger(4));
        s = _in33;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> EncodeRecursively(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _14227___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((b).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_14227___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _14227___accumulator = Dafny.Sequence<byte>.Concat(_14227___accumulator, Base64_Compile.__default.EncodeBlock((b).Take(new BigInteger(3))));
        Dafny.ISequence<byte> _in34 = (b).Drop(new BigInteger(3));
        b = _in34;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> FromCharsToIndices(Dafny.ISequence<char> s) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim7 = new BigInteger((s).Count);
        var arr7 = new byte[Dafny.Helpers.ToIntChecked(dim7,"C# array size must not be larger than max 32-bit int")];
        for (int i7 = 0; i7 < dim7; i7++) {
          var _14228_i = (BigInteger) i7;
          arr7[(int)(_14228_i)] = Base64_Compile.__default.CharToIndex((s).Select(_14228_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr7);
      }))();
    }
    public static Dafny.ISequence<char> FromIndicesToChars(Dafny.ISequence<byte> b) {
      return ((System.Func<Dafny.ISequence<char>>) (() => {
        BigInteger dim8 = new BigInteger((b).Count);
        var arr8 = new char[Dafny.Helpers.ToIntChecked(dim8,"C# array size must not be larger than max 32-bit int")];
        for (int i8 = 0; i8 < dim8; i8++) {
          var _14229_i = (BigInteger) i8;
          arr8[(int)(_14229_i)] = Base64_Compile.__default.IndexToChar((b).Select(_14229_i));
        }
        return Dafny.Sequence<char>.FromArray(arr8);
      }))();
    }
    public static Dafny.ISequence<byte> DecodeUnpadded(Dafny.ISequence<char> s) {
      return Base64_Compile.__default.DecodeRecursively(Base64_Compile.__default.FromCharsToIndices(s));
    }
    public static Dafny.ISequence<char> EncodeUnpadded(Dafny.ISequence<byte> b) {
      return Base64_Compile.__default.FromIndicesToChars(Base64_Compile.__default.EncodeRecursively(b));
    }
    public static bool Is1Padding(Dafny.ISequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (Base64_Compile.__default.IsBase64Char((s).Select(new BigInteger(2))))) && (((byte)((Base64_Compile.__default.CharToIndex((s).Select(new BigInteger(2)))) % (4))) == (0))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.ISequence<byte> Decode1Padding(Dafny.ISequence<char> s) {
      Dafny.ISequence<byte> _14230_d = Base64_Compile.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Base64_Compile.__default.CharToIndex((s).Select(BigInteger.Zero)), Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One)), Base64_Compile.__default.CharToIndex((s).Select(new BigInteger(2))), 0));
      return Dafny.Sequence<byte>.FromElements((_14230_d).Select(BigInteger.Zero), (_14230_d).Select(BigInteger.One));
    }
    public static Dafny.ISequence<char> Encode1Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _14231_e = Base64_Compile.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), (b).Select(BigInteger.One), 0));
      return Dafny.Sequence<char>.FromElements(Base64_Compile.__default.IndexToChar((_14231_e).Select(BigInteger.Zero)), Base64_Compile.__default.IndexToChar((_14231_e).Select(BigInteger.One)), Base64_Compile.__default.IndexToChar((_14231_e).Select(new BigInteger(2))), '=');
    }
    public static bool Is2Padding(Dafny.ISequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (((byte)((Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One))) % (16))) == (0))) && (((s).Select(new BigInteger(2))) == ('='))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.ISequence<byte> Decode2Padding(Dafny.ISequence<char> s) {
      Dafny.ISequence<byte> _14232_d = Base64_Compile.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Base64_Compile.__default.CharToIndex((s).Select(BigInteger.Zero)), Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One)), 0, 0));
      return Dafny.Sequence<byte>.FromElements((_14232_d).Select(BigInteger.Zero));
    }
    public static Dafny.ISequence<char> Encode2Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _14233_e = Base64_Compile.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), 0, 0));
      return Dafny.Sequence<char>.FromElements(Base64_Compile.__default.IndexToChar((_14233_e).Select(BigInteger.Zero)), Base64_Compile.__default.IndexToChar((_14233_e).Select(BigInteger.One)), '=', '=');
    }
    public static bool IsBase64String(Dafny.ISequence<char> s) {
      BigInteger _14234_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && ((Base64_Compile.__default.IsUnpaddedBase64String(s)) || ((Base64_Compile.__default.IsUnpaddedBase64String((s).Take(_14234_finalBlockStart))) && ((Base64_Compile.__default.Is1Padding((s).Drop(_14234_finalBlockStart))) || (Base64_Compile.__default.Is2Padding((s).Drop(_14234_finalBlockStart))))));
    }
    public static Dafny.ISequence<byte> DecodeValid(Dafny.ISequence<char> s) {
      if ((s).Equals((Dafny.Sequence<char>.FromElements()))) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        BigInteger _14235_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
        Dafny.ISequence<char> _14236_prefix = (s).Take(_14235_finalBlockStart);
        Dafny.ISequence<char> _14237_suffix = (s).Drop(_14235_finalBlockStart);
        if (Base64_Compile.__default.Is1Padding(_14237_suffix)) {
          return Dafny.Sequence<byte>.Concat(Base64_Compile.__default.DecodeUnpadded(_14236_prefix), Base64_Compile.__default.Decode1Padding(_14237_suffix));
        } else if (Base64_Compile.__default.Is2Padding(_14237_suffix)) {
          return Dafny.Sequence<byte>.Concat(Base64_Compile.__default.DecodeUnpadded(_14236_prefix), Base64_Compile.__default.Decode2Padding(_14237_suffix));
        } else {
          return Base64_Compile.__default.DecodeUnpadded(s);
        }
      }
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Decode(Dafny.ISequence<char> s) {
      if (Base64_Compile.__default.IsBase64String(s)) {
        return @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(Base64_Compile.__default.DecodeValid(s));
      } else {
        return @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("The encoding is malformed"));
      }
    }
    public static Dafny.ISequence<char> Encode(Dafny.ISequence<byte> b) {
      if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))).Sign == 0) {
        return Base64_Compile.__default.EncodeUnpadded(b);
      } else if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))) == (BigInteger.One)) {
        return Dafny.Sequence<char>.Concat(Base64_Compile.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (BigInteger.One))), Base64_Compile.__default.Encode2Padding((b).Drop((new BigInteger((b).Count)) - (BigInteger.One))));
      } else {
        return Dafny.Sequence<char>.Concat(Base64_Compile.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (new BigInteger(2)))), Base64_Compile.__default.Encode1Padding((b).Drop((new BigInteger((b).Count)) - (new BigInteger(2)))));
      }
    }
  }
} // end of namespace Base64_Compile
namespace MessageHeader {










  public class Header {
    public readonly MessageHeader.HeaderBody body;
    public readonly MessageHeader.HeaderAuthentication auth;
    public Header(MessageHeader.HeaderBody body, MessageHeader.HeaderAuthentication auth) {
      this.body = body;
      this.auth = auth;
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.Header;
      return oth != null && object.Equals(this.body, oth.body) && object.Equals(this.auth, oth.auth);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.auth));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.Header.Header";
      s += "(";
      s += Dafny.Helpers.ToString(this.body);
      s += ", ";
      s += Dafny.Helpers.ToString(this.auth);
      s += ")";
      return s;
    }
    private static readonly Header theDefault = create(MessageHeader.HeaderBody.Default(), MessageHeader.HeaderAuthentication.Default());
    public static Header Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageHeader.Header> _TYPE = new Dafny.TypeDescriptor<MessageHeader.Header>(MessageHeader.Header.Default());
    public static Dafny.TypeDescriptor<MessageHeader.Header> _TypeDescriptor() {
      return _TYPE;
    }
    public static Header create(MessageHeader.HeaderBody body, MessageHeader.HeaderAuthentication auth) {
      return new Header(body, auth);
    }
    public bool is_Header { get { return true; } }
    public MessageHeader.HeaderBody dtor_body {
      get {
        return this.body;
      }
    }
    public MessageHeader.HeaderAuthentication dtor_auth {
      get {
        return this.auth;
      }
    }
  }

  public partial class Version {
    private static readonly byte Witness = MessageHeader.__default.VERSION__1;
    public static byte Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(MessageHeader.Version.Default());
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class Type {
    private static readonly byte Witness = MessageHeader.__default.TYPE__CUSTOMER__AED;
    public static byte Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(MessageHeader.Type.Default());
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class MessageID {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(MessageHeader.MessageID.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public abstract class ContentType {
    public ContentType() { }
    private static readonly ContentType theDefault = create_NonFramed();
    public static ContentType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageHeader.ContentType> _TYPE = new Dafny.TypeDescriptor<MessageHeader.ContentType>(MessageHeader.ContentType.Default());
    public static Dafny.TypeDescriptor<MessageHeader.ContentType> _TypeDescriptor() {
      return _TYPE;
    }
    public static ContentType create_NonFramed() {
      return new ContentType_NonFramed();
    }
    public static ContentType create_Framed() {
      return new ContentType_Framed();
    }
    public bool is_NonFramed { get { return this is ContentType_NonFramed; } }
    public bool is_Framed { get { return this is ContentType_Framed; } }
    public static System.Collections.Generic.IEnumerable<ContentType> AllSingletonConstructors {
      get {
        yield return ContentType.create_NonFramed();
        yield return ContentType.create_Framed();
      }
    }
  }
  public class ContentType_NonFramed : ContentType {
    public ContentType_NonFramed() {
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.ContentType_NonFramed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.ContentType.NonFramed";
      return s;
    }
  }
  public class ContentType_Framed : ContentType {
    public ContentType_Framed() {
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.ContentType_Framed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.ContentType.Framed";
      return s;
    }
  }

  public class EncryptedDataKeys {
    public readonly Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> entries;
    public EncryptedDataKeys(Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> entries) {
      this.entries = entries;
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.EncryptedDataKeys;
      return oth != null && object.Equals(this.entries, oth.entries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.entries));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.EncryptedDataKeys.EncryptedDataKeys";
      s += "(";
      s += Dafny.Helpers.ToString(this.entries);
      s += ")";
      return s;
    }
    private static readonly EncryptedDataKeys theDefault = create(Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Empty);
    public static EncryptedDataKeys Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageHeader.EncryptedDataKeys> _TYPE = new Dafny.TypeDescriptor<MessageHeader.EncryptedDataKeys>(MessageHeader.EncryptedDataKeys.Default());
    public static Dafny.TypeDescriptor<MessageHeader.EncryptedDataKeys> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptedDataKeys create(Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> entries) {
      return new EncryptedDataKeys(entries);
    }
    public bool is_EncryptedDataKeys { get { return true; } }
    public Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> dtor_entries {
      get {
        return this.entries;
      }
    }
  }

  public class HeaderBody {
    public readonly byte version;
    public readonly byte typ;
    public readonly ushort algorithmSuiteID;
    public readonly Dafny.ISequence<byte> messageID;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> aad;
    public readonly MessageHeader.EncryptedDataKeys encryptedDataKeys;
    public readonly MessageHeader.ContentType contentType;
    public readonly byte ivLength;
    public readonly uint frameLength;
    public HeaderBody(byte version, byte typ, ushort algorithmSuiteID, Dafny.ISequence<byte> messageID, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> aad, MessageHeader.EncryptedDataKeys encryptedDataKeys, MessageHeader.ContentType contentType, byte ivLength, uint frameLength) {
      this.version = version;
      this.typ = typ;
      this.algorithmSuiteID = algorithmSuiteID;
      this.messageID = messageID;
      this.aad = aad;
      this.encryptedDataKeys = encryptedDataKeys;
      this.contentType = contentType;
      this.ivLength = ivLength;
      this.frameLength = frameLength;
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.HeaderBody;
      return oth != null && this.version == oth.version && this.typ == oth.typ && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.messageID, oth.messageID) && object.Equals(this.aad, oth.aad) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.contentType, oth.contentType) && this.ivLength == oth.ivLength && this.frameLength == oth.frameLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.version));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.messageID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.aad));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ivLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frameLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.HeaderBody.HeaderBody";
      s += "(";
      s += Dafny.Helpers.ToString(this.version);
      s += ", ";
      s += Dafny.Helpers.ToString(this.typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.messageID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.aad);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this.contentType);
      s += ", ";
      s += Dafny.Helpers.ToString(this.ivLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.frameLength);
      s += ")";
      return s;
    }
    private static readonly HeaderBody theDefault = create(MessageHeader.Version.Default(), MessageHeader.Type.Default(), AlgorithmSuite.ID.Witness, MessageHeader.MessageID.Default(), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, MessageHeader.EncryptedDataKeys.Default(), MessageHeader.ContentType.Default(), 0, 0);
    public static HeaderBody Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageHeader.HeaderBody> _TYPE = new Dafny.TypeDescriptor<MessageHeader.HeaderBody>(MessageHeader.HeaderBody.Default());
    public static Dafny.TypeDescriptor<MessageHeader.HeaderBody> _TypeDescriptor() {
      return _TYPE;
    }
    public static HeaderBody create(byte version, byte typ, ushort algorithmSuiteID, Dafny.ISequence<byte> messageID, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> aad, MessageHeader.EncryptedDataKeys encryptedDataKeys, MessageHeader.ContentType contentType, byte ivLength, uint frameLength) {
      return new HeaderBody(version, typ, algorithmSuiteID, messageID, aad, encryptedDataKeys, contentType, ivLength, frameLength);
    }
    public bool is_HeaderBody { get { return true; } }
    public byte dtor_version {
      get {
        return this.version;
      }
    }
    public byte dtor_typ {
      get {
        return this.typ;
      }
    }
    public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.ISequence<byte> dtor_messageID {
      get {
        return this.messageID;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_aad {
      get {
        return this.aad;
      }
    }
    public MessageHeader.EncryptedDataKeys dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public MessageHeader.ContentType dtor_contentType {
      get {
        return this.contentType;
      }
    }
    public byte dtor_ivLength {
      get {
        return this.ivLength;
      }
    }
    public uint dtor_frameLength {
      get {
        return this.frameLength;
      }
    }
  }

  public class HeaderAuthentication {
    public readonly Dafny.ISequence<byte> iv;
    public readonly Dafny.ISequence<byte> authenticationTag;
    public HeaderAuthentication(Dafny.ISequence<byte> iv, Dafny.ISequence<byte> authenticationTag) {
      this.iv = iv;
      this.authenticationTag = authenticationTag;
    }
    public override bool Equals(object other) {
      var oth = other as MessageHeader.HeaderAuthentication;
      return oth != null && object.Equals(this.iv, oth.iv) && object.Equals(this.authenticationTag, oth.authenticationTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authenticationTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageHeader_Compile.HeaderAuthentication.HeaderAuthentication";
      s += "(";
      s += Dafny.Helpers.ToString(this.iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authenticationTag);
      s += ")";
      return s;
    }
    private static readonly HeaderAuthentication theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static HeaderAuthentication Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageHeader.HeaderAuthentication> _TYPE = new Dafny.TypeDescriptor<MessageHeader.HeaderAuthentication>(MessageHeader.HeaderAuthentication.Default());
    public static Dafny.TypeDescriptor<MessageHeader.HeaderAuthentication> _TypeDescriptor() {
      return _TYPE;
    }
    public static HeaderAuthentication create(Dafny.ISequence<byte> iv, Dafny.ISequence<byte> authenticationTag) {
      return new HeaderAuthentication(iv, authenticationTag);
    }
    public bool is_HeaderAuthentication { get { return true; } }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        return this.iv;
      }
    }
    public Dafny.ISequence<byte> dtor_authenticationTag {
      get {
        return this.authenticationTag;
      }
    }
  }

  public partial class __default {
    public static byte ContentTypeToUInt8(MessageHeader.ContentType contentType) {
      MessageHeader.ContentType _source16 = contentType;
      if (_source16.is_NonFramed) {
        return 1;
      } else {
        return 2;
      }
    }
    public static Wrappers_Compile.Option<MessageHeader.ContentType> UInt8ToContentType(byte x) {
      if ((x) == (1)) {
        return @Wrappers_Compile.Option<MessageHeader.ContentType>.create_Some(@MessageHeader.ContentType.create_NonFramed());
      } else if ((x) == (2)) {
        return @Wrappers_Compile.Option<MessageHeader.ContentType>.create_Some(@MessageHeader.ContentType.create_Framed());
      } else {
        return @Wrappers_Compile.Option<MessageHeader.ContentType>.create_None();
      }
    }
    public static Dafny.ISequence<byte> EDKEntryToSeq(Dafny.Aws.Crypto.EncryptedDataKey edk) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)((edk).dtor_keyProviderId).Count), (edk).dtor_keyProviderId), StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)((edk).dtor_keyProviderInfo).Count)), (edk).dtor_keyProviderInfo), StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)((edk).dtor_ciphertext).Count)), (edk).dtor_ciphertext);
    }
    public static byte VERSION__1 { get {
      return 1;
    } }
    public static byte TYPE__CUSTOMER__AED { get {
      return 128;
    } }
    public static BigInteger MESSAGE__ID__LEN { get {
      return new BigInteger(16);
    } }
    public static Dafny.ISequence<byte> Reserved { get {
      return Dafny.Sequence<byte>.FromElements(0, 0, 0, 0);
    } }
  }
} // end of namespace MessageHeader
namespace Streams_Compile {



  public partial class SeqReader<T> {
    public SeqReader() {
      this.pos = BigInteger.Zero;
      this._data = Dafny.Sequence<T>.Empty;
    }
    public BigInteger pos;public void __ctor(Dafny.ISequence<T> s)
    {
      (this)._data = s;
      (this).pos = BigInteger.Zero;
    }
    public Dafny.ISequence<T> ReadElements(BigInteger n)
    {
      Dafny.ISequence<T> elems = Dafny.Sequence<T>.Empty;
      elems = (((this).data).Drop(this.pos)).Take(n);
      (this).pos = (this.pos) + (n);
      elems = elems;
      return elems;
      return elems;
    }
    public Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>> ReadExact(BigInteger n)
    {
      Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.Default(Dafny.Sequence<T>.Empty);
      if ((n) > ((new BigInteger(((this).data).Count)) - (this.pos))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Not enough elements left on stream."));
        return res;
      } else {
        Dafny.ISequence<T> _14238_elements;
        Dafny.ISequence<T> _out16;
        _out16 = (this).ReadElements(n);
        _14238_elements = _out16;
        res = @Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.create_Success(_14238_elements);
        return res;
      }
      return res;
    }
    public Dafny.ISequence<T> _data;public Dafny.ISequence<T> data { get {
      return this._data;
    } }
  }

  public partial class ByteReader {
    public ByteReader() {
      this._reader = default(Streams_Compile.SeqReader<byte>);
    }
    public void __ctor(Dafny.ISequence<byte> s)
    {
      Streams_Compile.SeqReader<byte> _14239_mr;
      Streams_Compile.SeqReader<byte> _nw5 = new Streams_Compile.SeqReader<byte>();
      _nw5.__ctor(s);
      _14239_mr = _nw5;
      (this)._reader = _14239_mr;
    }
    public Wrappers_Compile.Result<byte, Dafny.ISequence<char>> ReadByte()
    {
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> res = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _14240_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14241_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out17;
      _out17 = ((this).reader).ReadExact(BigInteger.One);
      _14241_valueOrError0 = _out17;
      if ((_14241_valueOrError0).IsFailure()) {
        res = (_14241_valueOrError0).PropagateFailure<byte>();
        return res;
      }
      _14240_bytes = (_14241_valueOrError0).Extract();
      res = @Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Success((_14240_bytes).Select(BigInteger.Zero));
      return res;
      return res;
    }
    public Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> ReadBytes(BigInteger n)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14242_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14243_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out18;
      _out18 = ((this).reader).ReadExact(n);
      _14243_valueOrError0 = _out18;
      if ((_14243_valueOrError0).IsFailure()) {
        res = (_14243_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14242_bytes = (_14243_valueOrError0).Extract();
      res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14242_bytes);
      return res;
      return res;
    }
    public Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> ReadUInt16()
    {
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> res = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _14244_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14245_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out19;
      _out19 = ((this).reader).ReadExact(new BigInteger(2));
      _14245_valueOrError0 = _out19;
      if ((_14245_valueOrError0).IsFailure()) {
        res = (_14245_valueOrError0).PropagateFailure<ushort>();
        return res;
      }
      _14244_bytes = (_14245_valueOrError0).Extract();
      ushort _14246_n;
      _14246_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt16(_14244_bytes);
      res = @Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.create_Success(_14246_n);
      return res;
      return res;
    }
    public Wrappers_Compile.Result<uint, Dafny.ISequence<char>> ReadUInt32()
    {
      Wrappers_Compile.Result<uint, Dafny.ISequence<char>> res = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _14247_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14248_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out20;
      _out20 = ((this).reader).ReadExact(new BigInteger(4));
      _14248_valueOrError0 = _out20;
      if ((_14248_valueOrError0).IsFailure()) {
        res = (_14248_valueOrError0).PropagateFailure<uint>();
        return res;
      }
      _14247_bytes = (_14248_valueOrError0).Extract();
      uint _14249_n;
      _14249_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt32(_14247_bytes);
      res = @Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.create_Success(_14249_n);
      return res;
      return res;
    }
    public Wrappers_Compile.Result<ulong, Dafny.ISequence<char>> ReadUInt64()
    {
      Wrappers_Compile.Result<ulong, Dafny.ISequence<char>> res = Wrappers_Compile.Result<ulong, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _14250_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14251_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out21;
      _out21 = ((this).reader).ReadExact(new BigInteger(8));
      _14251_valueOrError0 = _out21;
      if ((_14251_valueOrError0).IsFailure()) {
        res = (_14251_valueOrError0).PropagateFailure<ulong>();
        return res;
      }
      _14250_bytes = (_14251_valueOrError0).Extract();
      ulong _14252_n;
      _14252_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt64(_14250_bytes);
      res = @Wrappers_Compile.Result<ulong, Dafny.ISequence<char>>.create_Success(_14252_n);
      return res;
      return res;
    }
    public bool IsDoneReading()
    {
      bool b = false;
      b = (new BigInteger((((this).reader).data).Count)) == ((this).reader.pos);
      return b;
      return b;
    }
    public BigInteger GetSizeRead()
    {
      BigInteger n = BigInteger.Zero;
      n = (this).reader.pos;
      return n;
      return n;
    }
    public Streams_Compile.SeqReader<byte> _reader;public Streams_Compile.SeqReader<byte> reader { get {
      return this._reader;
    } }
  }

  public partial class SeqWriter<T> {
    public SeqWriter() {
      this.data = Dafny.Sequence<T>.Empty;
    }
    public Dafny.ISequence<T> data;public void __ctor()
    {
      (this).data = Dafny.Sequence<T>.FromElements();
    }
    public BigInteger WriteElements(Dafny.ISequence<T> elems)
    {
      BigInteger n = BigInteger.Zero;
      (this).data = Dafny.Sequence<T>.Concat(this.data, elems);
      n = new BigInteger((elems).Count);
      return n;
      return n;
    }
  }

  public partial class ByteWriter {
    public ByteWriter() {
      this._writer = default(Streams_Compile.SeqWriter<byte>);
    }
    public void __ctor()
    {
      Streams_Compile.SeqWriter<byte> _14253_mw;
      Streams_Compile.SeqWriter<byte> _nw6 = new Streams_Compile.SeqWriter<byte>();
      _nw6.__ctor();
      _14253_mw = _nw6;
      (this)._writer = _14253_mw;
    }
    public BigInteger WriteByte(byte n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out22;
      _out22 = ((this).writer).WriteElements(Dafny.Sequence<byte>.FromElements(n));
      r = _out22;
      return r;
    }
    public BigInteger WriteBytes(Dafny.ISequence<byte> s)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out23;
      _out23 = ((this).writer).WriteElements(s);
      r = _out23;
      return r;
    }
    public BigInteger WriteUInt16(ushort n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out24;
      _out24 = ((this).writer).WriteElements(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq(n));
      r = _out24;
      return r;
    }
    public BigInteger WriteUInt32(uint n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out25;
      _out25 = ((this).writer).WriteElements(StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(n));
      r = _out25;
      return r;
    }
    public Dafny.ISequence<byte> GetDataWritten() {
      return (this).writer.data;
    }
    public BigInteger GetSizeWritten() {
      return new BigInteger(((this).writer.data).Count);
    }
    public Streams_Compile.SeqWriter<byte> _writer;public Streams_Compile.SeqWriter<byte> writer { get {
      return this._writer;
    } }
  }

} // end of namespace Streams_Compile
namespace Deserialize_Compile {












  public class DeserializeHeaderResult {
    public readonly MessageHeader.Header header;
    public DeserializeHeaderResult(MessageHeader.Header header) {
      this.header = header;
    }
    public override bool Equals(object other) {
      var oth = other as Deserialize_Compile.DeserializeHeaderResult;
      return oth != null && object.Equals(this.header, oth.header);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.header));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Deserialize_Compile.DeserializeHeaderResult.DeserializeHeaderResult";
      s += "(";
      s += Dafny.Helpers.ToString(this.header);
      s += ")";
      return s;
    }
    private static readonly DeserializeHeaderResult theDefault = create(MessageHeader.Header.Default());
    public static DeserializeHeaderResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Deserialize_Compile.DeserializeHeaderResult> _TYPE = new Dafny.TypeDescriptor<Deserialize_Compile.DeserializeHeaderResult>(Deserialize_Compile.DeserializeHeaderResult.Default());
    public static Dafny.TypeDescriptor<Deserialize_Compile.DeserializeHeaderResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static DeserializeHeaderResult create(MessageHeader.Header header) {
      return new DeserializeHeaderResult(header);
    }
    public bool is_DeserializeHeaderResult { get { return true; } }
    public MessageHeader.Header dtor_header {
      get {
        return this.header;
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>> DeserializeHeader(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>>.Default(Deserialize_Compile.DeserializeHeaderResult.Default());
      MessageHeader.HeaderBody _14254_hb = MessageHeader.HeaderBody.Default();
      Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>> _14255_valueOrError0 = Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.Default(MessageHeader.HeaderBody.Default());
      Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>> _out26;
      _out26 = Deserialize_Compile.__default.DeserializeHeaderBody(rd);
      _14255_valueOrError0 = _out26;
      if ((_14255_valueOrError0).IsFailure()) {
        res = (_14255_valueOrError0).PropagateFailure<Deserialize_Compile.DeserializeHeaderResult>();
        return res;
      }
      _14254_hb = (_14255_valueOrError0).Extract();
      MessageHeader.HeaderAuthentication _14256_auth = MessageHeader.HeaderAuthentication.Default();
      Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>> _14257_valueOrError1 = Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>>.Default(MessageHeader.HeaderAuthentication.Default());
      Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>> _out27;
      _out27 = Deserialize_Compile.__default.DeserializeHeaderAuthentication(rd, (_14254_hb).dtor_algorithmSuiteID);
      _14257_valueOrError1 = _out27;
      if ((_14257_valueOrError1).IsFailure()) {
        res = (_14257_valueOrError1).PropagateFailure<Deserialize_Compile.DeserializeHeaderResult>();
        return res;
      }
      _14256_auth = (_14257_valueOrError1).Extract();
      res = @Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>>.create_Success(@Deserialize_Compile.DeserializeHeaderResult.create(@MessageHeader.Header.create(_14254_hb, _14256_auth)));
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>> DeserializeHeaderBody(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.Default(MessageHeader.HeaderBody.Default());
      byte _14258_version = MessageHeader.Version.Default();
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14259_valueOrError0 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(MessageHeader.Version.Default());
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out28;
      _out28 = Deserialize_Compile.__default.DeserializeVersion(rd);
      _14259_valueOrError0 = _out28;
      if ((_14259_valueOrError0).IsFailure()) {
        ret = (_14259_valueOrError0).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14258_version = (_14259_valueOrError0).Extract();
      byte _14260_typ = MessageHeader.Type.Default();
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14261_valueOrError1 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(MessageHeader.Type.Default());
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out29;
      _out29 = Deserialize_Compile.__default.DeserializeType(rd);
      _14261_valueOrError1 = _out29;
      if ((_14261_valueOrError1).IsFailure()) {
        ret = (_14261_valueOrError1).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14260_typ = (_14261_valueOrError1).Extract();
      ushort _14262_algorithmSuiteID = AlgorithmSuite.ID.Witness;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14263_valueOrError2 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(AlgorithmSuite.ID.Witness);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out30;
      _out30 = Deserialize_Compile.__default.DeserializeAlgorithmSuiteID(rd);
      _14263_valueOrError2 = _out30;
      if ((_14263_valueOrError2).IsFailure()) {
        ret = (_14263_valueOrError2).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14262_algorithmSuiteID = (_14263_valueOrError2).Extract();
      Dafny.ISequence<byte> _14264_messageID = MessageHeader.MessageID.Default();
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14265_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(MessageHeader.MessageID.Default());
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out31;
      _out31 = Deserialize_Compile.__default.DeserializeMsgID(rd);
      _14265_valueOrError3 = _out31;
      if ((_14265_valueOrError3).IsFailure()) {
        ret = (_14265_valueOrError3).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14264_messageID = (_14265_valueOrError3).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _14266_aad = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _14267_valueOrError4 = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.Default(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
      Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _out32;
      _out32 = Deserialize_Compile.__default.DeserializeAAD(rd);
      _14267_valueOrError4 = _out32;
      if ((_14267_valueOrError4).IsFailure()) {
        ret = (_14267_valueOrError4).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14266_aad = (_14267_valueOrError4).Extract();
      MessageHeader.EncryptedDataKeys _14268_encryptedDataKeys = MessageHeader.EncryptedDataKeys.Default();
      Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>> _14269_valueOrError5 = Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>>.Default(MessageHeader.EncryptedDataKeys.Default());
      Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>> _out33;
      _out33 = Deserialize_Compile.__default.DeserializeEncryptedDataKeys(rd);
      _14269_valueOrError5 = _out33;
      if ((_14269_valueOrError5).IsFailure()) {
        ret = (_14269_valueOrError5).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14268_encryptedDataKeys = (_14269_valueOrError5).Extract();
      MessageHeader.ContentType _14270_contentType = MessageHeader.ContentType.Default();
      Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>> _14271_valueOrError6 = Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>>.Default(MessageHeader.ContentType.Default());
      Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>> _out34;
      _out34 = Deserialize_Compile.__default.DeserializeContentType(rd);
      _14271_valueOrError6 = _out34;
      if ((_14271_valueOrError6).IsFailure()) {
        ret = (_14271_valueOrError6).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14270_contentType = (_14271_valueOrError6).Extract();
      Dafny.ISequence<byte> _14272___v2 = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14273_valueOrError7 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out35;
      _out35 = Deserialize_Compile.__default.DeserializeReserved(rd);
      _14273_valueOrError7 = _out35;
      if ((_14273_valueOrError7).IsFailure()) {
        ret = (_14273_valueOrError7).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14272___v2 = (_14273_valueOrError7).Extract();
      byte _14274_ivLength = 0;
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14275_valueOrError8 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out36;
      _out36 = (rd).ReadByte();
      _14275_valueOrError8 = _out36;
      if ((_14275_valueOrError8).IsFailure()) {
        ret = (_14275_valueOrError8).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14274_ivLength = (_14275_valueOrError8).Extract();
      uint _14276_frameLength = 0;
      Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _14277_valueOrError9 = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _out37;
      _out37 = (rd).ReadUInt32();
      _14277_valueOrError9 = _out37;
      if ((_14277_valueOrError9).IsFailure()) {
        ret = (_14277_valueOrError9).PropagateFailure<MessageHeader.HeaderBody>();
        return ret;
      }
      _14276_frameLength = (_14277_valueOrError9).Extract();
      if ((new BigInteger(_14274_ivLength)) != (AlgorithmSuite.ID.IVLength(_14262_algorithmSuiteID))) {
        ret = @Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Incorrect IV length."));
        return ret;
      }
      if (((_14270_contentType).is_NonFramed) && ((_14276_frameLength) != (0U))) {
        ret = @Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Frame length must be 0 when content type is non-framed."));
        return ret;
      } else if (((_14270_contentType).is_Framed) && ((_14276_frameLength) == (0U))) {
        ret = @Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Frame length must be non-0 when content type is framed."));
        return ret;
      }
      MessageHeader.HeaderBody _14278_hb;
      _14278_hb = @MessageHeader.HeaderBody.create(_14258_version, _14260_typ, _14262_algorithmSuiteID, _14264_messageID, _14266_aad, _14268_encryptedDataKeys, _14270_contentType, _14274_ivLength, _14276_frameLength);
      ret = @Wrappers_Compile.Result<MessageHeader.HeaderBody, Dafny.ISequence<char>>.create_Success(_14278_hb);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>> DeserializeHeaderAuthentication(Streams_Compile.ByteReader rd, ushort algorithmSuiteID)
    {
      Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>>.Default(MessageHeader.HeaderAuthentication.Default());
      Dafny.ISequence<byte> _14279_iv = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14280_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out38;
      _out38 = (rd).ReadBytes(AlgorithmSuite.ID.IVLength(algorithmSuiteID));
      _14280_valueOrError0 = _out38;
      if ((_14280_valueOrError0).IsFailure()) {
        ret = (_14280_valueOrError0).PropagateFailure<MessageHeader.HeaderAuthentication>();
        return ret;
      }
      _14279_iv = (_14280_valueOrError0).Extract();
      Dafny.ISequence<byte> _14281_authenticationTag = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14282_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out39;
      _out39 = (rd).ReadBytes(AlgorithmSuite.ID.TagLength(algorithmSuiteID));
      _14282_valueOrError1 = _out39;
      if ((_14282_valueOrError1).IsFailure()) {
        ret = (_14282_valueOrError1).PropagateFailure<MessageHeader.HeaderAuthentication>();
        return ret;
      }
      _14281_authenticationTag = (_14282_valueOrError1).Extract();
      ret = @Wrappers_Compile.Result<MessageHeader.HeaderAuthentication, Dafny.ISequence<char>>.create_Success(@MessageHeader.HeaderAuthentication.create(_14279_iv, _14281_authenticationTag));
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<byte, Dafny.ISequence<char>> DeserializeVersion(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(MessageHeader.Version.Default());
      byte _14283_version = 0;
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14284_valueOrError0 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out40;
      _out40 = (rd).ReadByte();
      _14284_valueOrError0 = _out40;
      if ((_14284_valueOrError0).IsFailure()) {
        ret = (_14284_valueOrError0).PropagateFailure<byte>();
        return ret;
      }
      _14283_version = (_14284_valueOrError0).Extract();
      if ((_14283_version) == (MessageHeader.__default.VERSION__1)) {
        ret = @Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Success(_14283_version);
        return ret;
      } else {
        ret = @Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Version not supported."));
        return ret;
      }
      return ret;
    }
    public static Wrappers_Compile.Result<byte, Dafny.ISequence<char>> DeserializeType(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(MessageHeader.Type.Default());
      byte _14285_typ = 0;
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14286_valueOrError0 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out41;
      _out41 = (rd).ReadByte();
      _14286_valueOrError0 = _out41;
      if ((_14286_valueOrError0).IsFailure()) {
        ret = (_14286_valueOrError0).PropagateFailure<byte>();
        return ret;
      }
      _14285_typ = (_14286_valueOrError0).Extract();
      if ((_14285_typ) == (MessageHeader.__default.TYPE__CUSTOMER__AED)) {
        ret = @Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Success(_14285_typ);
        return ret;
      } else {
        ret = @Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Type not supported."));
        return ret;
      }
      return ret;
    }
    public static Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> DeserializeAlgorithmSuiteID(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(AlgorithmSuite.ID.Witness);
      ushort _14287_algorithmSuiteID = 0;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14288_valueOrError0 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out42;
      _out42 = (rd).ReadUInt16();
      _14288_valueOrError0 = _out42;
      if ((_14288_valueOrError0).IsFailure()) {
        ret = (_14288_valueOrError0).PropagateFailure<ushort>();
        return ret;
      }
      _14287_algorithmSuiteID = (_14288_valueOrError0).Extract();
      if ((AlgorithmSuite.__default.VALID__IDS).Contains((_14287_algorithmSuiteID))) {
        ret = @Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.create_Success((ushort)(_14287_algorithmSuiteID));
        return ret;
      } else {
        ret = @Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Algorithm suite not supported."));
        return ret;
      }
      return ret;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> DeserializeMsgID(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(MessageHeader.MessageID.Default());
      Dafny.ISequence<byte> _14289_msgID = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14290_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out43;
      _out43 = (rd).ReadBytes(MessageHeader.__default.MESSAGE__ID__LEN);
      _14290_valueOrError0 = _out43;
      if ((_14290_valueOrError0).IsFailure()) {
        ret = (_14290_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return ret;
      }
      _14289_msgID = (_14290_valueOrError0).Extract();
      ret = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14289_msgID);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> DeserializeUTF8(Streams_Compile.ByteReader rd, BigInteger n)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      Dafny.ISequence<byte> _14291_bytes = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14292_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out44;
      _out44 = (rd).ReadBytes(n);
      _14292_valueOrError0 = _out44;
      if ((_14292_valueOrError0).IsFailure()) {
        ret = (_14292_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return ret;
      }
      _14291_bytes = (_14292_valueOrError0).Extract();
      if (UTF8.__default.ValidUTF8Seq(_14291_bytes)) {
        Dafny.ISequence<byte> _14293_utf8;
        _14293_utf8 = _14291_bytes;
        ret = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14293_utf8);
        return ret;
      } else {
        ret = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Not a valid UTF8 string."));
        return ret;
      }
      return ret;
    }
    public static Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> DeserializeAAD(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.Default(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
      ushort _14294_kvPairsLength = 0;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14295_valueOrError0 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out45;
      _out45 = (rd).ReadUInt16();
      _14295_valueOrError0 = _out45;
      if ((_14295_valueOrError0).IsFailure()) {
        ret = (_14295_valueOrError0).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
        return ret;
      }
      _14294_kvPairsLength = (_14295_valueOrError0).Extract();
      if ((_14294_kvPairsLength) == (0)) {
        ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements());
        return ret;
      } else if ((_14294_kvPairsLength) < (2)) {
        ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: The number of bytes in encryption context exceeds the given length."));
        return ret;
      }
      BigInteger _14296_totalBytesRead;
      _14296_totalBytesRead = BigInteger.Zero;
      ushort _14297_kvPairsCount = 0;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14298_valueOrError1 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out46;
      _out46 = (rd).ReadUInt16();
      _14298_valueOrError1 = _out46;
      if ((_14298_valueOrError1).IsFailure()) {
        ret = (_14298_valueOrError1).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
        return ret;
      }
      _14297_kvPairsCount = (_14298_valueOrError1).Extract();
      _14296_totalBytesRead = (_14296_totalBytesRead) + (new BigInteger(2));
      if ((_14297_kvPairsCount) == (0)) {
        ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Key value pairs count is 0."));
        return ret;
      }
      Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14299_kvPairs;
      _14299_kvPairs = Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromElements();
      ushort _14300_i;
      _14300_i = 0;
      while ((_14300_i) < (_14297_kvPairsCount)) {
        ushort _14301_keyLength = 0;
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14302_valueOrError2 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out47;
        _out47 = (rd).ReadUInt16();
        _14302_valueOrError2 = _out47;
        if ((_14302_valueOrError2).IsFailure()) {
          ret = (_14302_valueOrError2).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
          return ret;
        }
        _14301_keyLength = (_14302_valueOrError2).Extract();
        _14296_totalBytesRead = (_14296_totalBytesRead) + (new BigInteger(2));
        Dafny.ISequence<byte> _14303_key = UTF8.ValidUTF8Bytes.Default();
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14304_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out48;
        _out48 = Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_14301_keyLength));
        _14304_valueOrError3 = _out48;
        if ((_14304_valueOrError3).IsFailure()) {
          ret = (_14304_valueOrError3).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
          return ret;
        }
        _14303_key = (_14304_valueOrError3).Extract();
        _14296_totalBytesRead = (_14296_totalBytesRead) + (new BigInteger((_14303_key).Count));
        ushort _14305_valueLength = 0;
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14306_valueOrError4 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out49;
        _out49 = (rd).ReadUInt16();
        _14306_valueOrError4 = _out49;
        if ((_14306_valueOrError4).IsFailure()) {
          ret = (_14306_valueOrError4).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
          return ret;
        }
        _14305_valueLength = (_14306_valueOrError4).Extract();
        _14296_totalBytesRead = (_14296_totalBytesRead) + (new BigInteger(2));
        if ((new BigInteger(_14294_kvPairsLength)) < ((_14296_totalBytesRead) + (new BigInteger(_14305_valueLength)))) {
          ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: The number of bytes in encryption context exceeds the given length."));
          return ret;
        }
        Dafny.ISequence<byte> _14307_value = UTF8.ValidUTF8Bytes.Default();
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14308_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out50;
        _out50 = Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_14305_valueLength));
        _14308_valueOrError5 = _out50;
        if ((_14308_valueOrError5).IsFailure()) {
          ret = (_14308_valueOrError5).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
          return ret;
        }
        _14307_value = (_14308_valueOrError5).Extract();
        _14296_totalBytesRead = (_14296_totalBytesRead) + (new BigInteger((_14307_value).Count));
        Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> _14309_opt;
        Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> _out51;
        _out51 = Deserialize_Compile.__default.InsertNewEntry(_14299_kvPairs, _14303_key, _14307_value);
        _14309_opt = _out51;
        Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> _source17 = _14309_opt;
        if (_source17.is_None) {
          {
            ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Duplicate key."));
            return ret;
          }
        } else {
          Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14310___mcc_h2 = ((Wrappers_Compile.Option_Some<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>)_source17).@value;
          {
            Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14311_kvPairs__ = _14310___mcc_h2;
            _14299_kvPairs = _14311_kvPairs__;
          }
        }
        _14300_i = (ushort)((_14300_i) + (1));
      }
      if ((new BigInteger(_14294_kvPairsLength)) != (_14296_totalBytesRead)) {
        ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Bytes actually read differs from bytes supposed to be read."));
        return ret;
      }
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _14312_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out52;
      _out52 = EncryptionContext.__default.LinearToMap(_14299_kvPairs);
      _14312_encryptionContext = _out52;
      bool _14313_isValid;
      bool _out53;
      _out53 = EncryptionContext.__default.CheckSerializable(_14312_encryptionContext);
      _14313_isValid = _out53;
      if ((!(_14313_isValid)) || ((new BigInteger((_14299_kvPairs).Count)) != (new BigInteger((_14312_encryptionContext).Count)))) {
        ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Failed to parse encryption context."));
        return ret;
      }
      ret = @Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(_14312_encryptionContext);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> InsertNewEntry(Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> kvPairs, Dafny.ISequence<byte> key, Dafny.ISequence<byte> @value)
    {
      Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> res = Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>.Default();
      BigInteger _14314_n;
      _14314_n = new BigInteger((kvPairs).Count);
      while (((_14314_n).Sign == 1) && (StandardLibrary_Compile.__default.LexicographicLessOrEqual<byte>(key, ((kvPairs).Select((_14314_n) - (BigInteger.One))).dtor__0, StandardLibrary_mUInt_Compile.__default.UInt8Less))) {
        _14314_n = (_14314_n) - (BigInteger.One);
      }
      if (((!(kvPairs).Equals((Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromElements()))) && (StandardLibrary_Compile.__default.LexicographicLessOrEqual<byte>(key, ((kvPairs).Select((new BigInteger((kvPairs).Count)) - (BigInteger.One))).dtor__0, StandardLibrary_mUInt_Compile.__default.UInt8Less))) && ((((kvPairs).Select(_14314_n)).dtor__0).Equals((key)))) {
        Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> _rhs0 = @Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>.create_None();
        res = _rhs0;
        return res;
      } else {
        Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>> _14315_kvPairs_k;
        _14315_kvPairs_k = Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.Concat(Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.Concat((kvPairs).Take(_14314_n), Dafny.Sequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>.FromElements(@_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create(key, @value))), (kvPairs).Drop(_14314_n));
        Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>> _rhs1 = @Wrappers_Compile.Option<Dafny.ISequence<_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>>.create_Some(_14315_kvPairs_k);
        res = _rhs1;
        return res;
      }
      return res;
    }
    public static Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>> DeserializeEncryptedDataKeys(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>>.Default(MessageHeader.EncryptedDataKeys.Default());
      ushort _14316_edkCount = 0;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14317_valueOrError0 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out54;
      _out54 = (rd).ReadUInt16();
      _14317_valueOrError0 = _out54;
      if ((_14317_valueOrError0).IsFailure()) {
        ret = (_14317_valueOrError0).PropagateFailure<MessageHeader.EncryptedDataKeys>();
        return ret;
      }
      _14316_edkCount = (_14317_valueOrError0).Extract();
      if ((_14316_edkCount) == (0)) {
        ret = @Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Encrypted data key count is 0."));
        return ret;
      }
      Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> _14318_edkEntries;
      _14318_edkEntries = Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromElements();
      ushort _14319_i;
      _14319_i = 0;
      while ((_14319_i) < (_14316_edkCount)) {
        ushort _14320_providerIdLength = 0;
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14321_valueOrError1 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out55;
        _out55 = (rd).ReadUInt16();
        _14321_valueOrError1 = _out55;
        if ((_14321_valueOrError1).IsFailure()) {
          ret = (_14321_valueOrError1).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14320_providerIdLength = (_14321_valueOrError1).Extract();
        Dafny.ISequence<byte> _14322_str = UTF8.ValidUTF8Bytes.Default();
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14323_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out56;
        _out56 = Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_14320_providerIdLength));
        _14323_valueOrError2 = _out56;
        if ((_14323_valueOrError2).IsFailure()) {
          ret = (_14323_valueOrError2).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14322_str = (_14323_valueOrError2).Extract();
        Dafny.ISequence<byte> _14324_providerId;
        _14324_providerId = _14322_str;
        ushort _14325_providerInfoLength = 0;
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14326_valueOrError3 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out57;
        _out57 = (rd).ReadUInt16();
        _14326_valueOrError3 = _out57;
        if ((_14326_valueOrError3).IsFailure()) {
          ret = (_14326_valueOrError3).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14325_providerInfoLength = (_14326_valueOrError3).Extract();
        Dafny.ISequence<byte> _14327_providerInfo = Dafny.Sequence<byte>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14328_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out58;
        _out58 = (rd).ReadBytes(new BigInteger(_14325_providerInfoLength));
        _14328_valueOrError4 = _out58;
        if ((_14328_valueOrError4).IsFailure()) {
          ret = (_14328_valueOrError4).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14327_providerInfo = (_14328_valueOrError4).Extract();
        ushort _14329_ciphertextLength = 0;
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14330_valueOrError5 = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out59;
        _out59 = (rd).ReadUInt16();
        _14330_valueOrError5 = _out59;
        if ((_14330_valueOrError5).IsFailure()) {
          ret = (_14330_valueOrError5).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14329_ciphertextLength = (_14330_valueOrError5).Extract();
        Dafny.ISequence<byte> _14331_ciphertext = Dafny.Sequence<byte>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14332_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out60;
        _out60 = (rd).ReadBytes(new BigInteger(_14329_ciphertextLength));
        _14332_valueOrError6 = _out60;
        if ((_14332_valueOrError6).IsFailure()) {
          ret = (_14332_valueOrError6).PropagateFailure<MessageHeader.EncryptedDataKeys>();
          return ret;
        }
        _14331_ciphertext = (_14332_valueOrError6).Extract();
        _14318_edkEntries = Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Concat(_14318_edkEntries, Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromElements(@Dafny.Aws.Crypto.EncryptedDataKey.create(_14324_providerId, _14327_providerInfo, _14331_ciphertext)));
        _14319_i = (ushort)((_14319_i) + (1));
      }
      MessageHeader.EncryptedDataKeys _14333_edks;
      _14333_edks = @MessageHeader.EncryptedDataKeys.create(_14318_edkEntries);
      ret = @Wrappers_Compile.Result<MessageHeader.EncryptedDataKeys, Dafny.ISequence<char>>.create_Success(_14333_edks);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>> DeserializeContentType(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>>.Default(MessageHeader.ContentType.Default());
      byte _14334_byte = 0;
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _14335_valueOrError0 = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<byte, Dafny.ISequence<char>> _out61;
      _out61 = (rd).ReadByte();
      _14335_valueOrError0 = _out61;
      if ((_14335_valueOrError0).IsFailure()) {
        ret = (_14335_valueOrError0).PropagateFailure<MessageHeader.ContentType>();
        return ret;
      }
      _14334_byte = (_14335_valueOrError0).Extract();
      Wrappers_Compile.Option<MessageHeader.ContentType> _source18 = MessageHeader.__default.UInt8ToContentType(_14334_byte);
      if (_source18.is_None) {
        {
          ret = @Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Content type not supported."));
          return ret;
        }
      } else {
        MessageHeader.ContentType _14336___mcc_h2 = ((Wrappers_Compile.Option_Some<MessageHeader.ContentType>)_source18).@value;
        {
          MessageHeader.ContentType _14337_contentType = _14336___mcc_h2;
          ret = @Wrappers_Compile.Result<MessageHeader.ContentType, Dafny.ISequence<char>>.create_Success(_14337_contentType);
          return ret;
        }
      }
      return ret;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> DeserializeReserved(Streams_Compile.ByteReader rd)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14338_reserved = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14339_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out62;
      _out62 = (rd).ReadBytes(new BigInteger(4));
      _14339_valueOrError0 = _out62;
      if ((_14339_valueOrError0).IsFailure()) {
        ret = (_14339_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return ret;
      }
      _14338_reserved = (_14339_valueOrError0).Extract();
      if ((_14338_reserved).Equals((MessageHeader.__default.Reserved))) {
        ret = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14338_reserved);
        return ret;
      } else {
        ret = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Reserved fields must be 0."));
        return ret;
      }
      return ret;
    }
  }
} // end of namespace Deserialize_Compile
namespace DefaultCMMDef {












  public partial class DefaultCMM : Dafny.Aws.Crypto.ICryptographicMaterialsManager {
    public DefaultCMM() {
      this._keyring = default(Dafny.Aws.Crypto.IKeyring);
    }
    public void OfKeyring(Dafny.Aws.Crypto.IKeyring k)
    {
      (this)._keyring = k;
    }
    public Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>> GetEncryptionMaterials(Dafny.Aws.Crypto.GetEncryptionMaterialsInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.GetEncryptionMaterialsOutput.Default());
      Dafny.ISequence<byte> _14340_reservedField;
      _14340_reservedField = Materials.__default.EC__PUBLIC__KEY__FIELD;
      if ((((input).dtor_encryptionContext).Keys).Contains((_14340_reservedField))) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Reserved Field found in EncryptionContext keys."));
        return res;
      }
      ushort _14341_id;
      _14341_id = AlgorithmSuite.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384;
      if (((input).dtor_algorithmSuiteId).is_Some) {
        _14341_id = AlgorithmSuite.__default.PolymorphIDToInternalID(((input).dtor_algorithmSuiteId).dtor_value);
      }
      Wrappers_Compile.Option<Dafny.ISequence<byte>> _14342_enc__sk;
      _14342_enc__sk = @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _14343_enc__ctx;
      _14343_enc__ctx = (input).dtor_encryptionContext;
      Wrappers_Compile.Option<Signature.ECDSAParams> _source19 = AlgorithmSuite.ID.SignatureType(_14341_id);
      if (_source19.is_None) {
      } else {
        Signature.ECDSAParams _14344___mcc_h1 = ((Wrappers_Compile.Option_Some<Signature.ECDSAParams>)_source19).@value;
        {
          Signature.ECDSAParams _14345_param = _14344___mcc_h1;
          Signature.SignatureKeyPair _14346_signatureKeys = Signature.SignatureKeyPair.Default();
          Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> _14347_valueOrError0 = Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>>.Default(Signature.SignatureKeyPair.Default());
          Wrappers_Compile.Result<Signature.SignatureKeyPair, Dafny.ISequence<char>> _out63;
          _out63 = Signature.__default.KeyGen(_14345_param);
          _14347_valueOrError0 = _out63;
          if ((_14347_valueOrError0).IsFailure()) {
            res = (_14347_valueOrError0).PropagateFailure<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput>();
            return res;
          }
          _14346_signatureKeys = (_14347_valueOrError0).Extract();
          _14342_enc__sk = @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((_14346_signatureKeys).dtor_signingKey);
          Dafny.ISequence<byte> _14348_enc__vk = UTF8.ValidUTF8Bytes.Default();
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14349_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out64;
          _out64 = UTF8.__default.Encode(Base64_Compile.__default.Encode((_14346_signatureKeys).dtor_verificationKey));
          _14349_valueOrError1 = _out64;
          if ((_14349_valueOrError1).IsFailure()) {
            res = (_14349_valueOrError1).PropagateFailure<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput>();
            return res;
          }
          _14348_enc__vk = (_14349_valueOrError1).Extract();
          _14343_enc__ctx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Update(_14343_enc__ctx,_14340_reservedField, _14348_enc__vk);
        }
      }
      bool _14350_validAAD;
      bool _out65;
      _out65 = EncryptionContext.__default.CheckSerializable(_14343_enc__ctx);
      _14350_validAAD = _out65;
      if (!(_14350_validAAD)) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Invalid Encryption Context"));
        return res;
      }
      Dafny.Aws.Crypto.EncryptionMaterials _14351_materials;
      _14351_materials = @Dafny.Aws.Crypto.EncryptionMaterials.create(AlgorithmSuite.__default.InternalIDToPolymorphID(_14341_id), _14343_enc__ctx, Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromElements(), @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), _14342_enc__sk);
      Dafny.Aws.Crypto.OnEncryptOutput _14352_result = Dafny.Aws.Crypto.OnEncryptOutput.Default();
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>> _14353_valueOrError2 = Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.OnEncryptOutput.Default());
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>> _out66;
      _out66 = ((this).keyring).OnEncrypt(@Dafny.Aws.Crypto.OnEncryptInput.create(_14351_materials));
      _14353_valueOrError2 = _out66;
      if ((_14353_valueOrError2).IsFailure()) {
        res = (_14353_valueOrError2).PropagateFailure<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput>();
        return res;
      }
      _14352_result = (_14353_valueOrError2).Extract();
      if (((((_14352_result).dtor_materials).dtor_plaintextDataKey).is_None) || ((new BigInteger((((_14352_result).dtor_materials).dtor_encryptedDataKeys).Count)).Sign == 0)) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Could not retrieve materials required for encryption"));
        return res;
      }
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14354_valueOrError3 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _14354_valueOrError3 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((this).OnEncryptResultValid(input, _14352_result), Dafny.Sequence<char>.FromString("Keyring returned an invalid response"));
      if ((_14354_valueOrError3).IsFailure()) {
        res = (_14354_valueOrError3).PropagateFailure<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput>();
        return res;
      }
      res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.GetEncryptionMaterialsOutput.create((_14352_result).dtor_materials));
      return res;
      return res;
    }
    public Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>> DecryptMaterials(Dafny.Aws.Crypto.DecryptMaterialsInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.DecryptMaterialsOutput.Default());
      Wrappers_Compile.Option<Dafny.ISequence<byte>> _14355_vkey;
      _14355_vkey = @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None();
      ushort _14356_algID;
      _14356_algID = AlgorithmSuite.__default.PolymorphIDToInternalID((input).dtor_algorithmSuiteId);
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _14357_encCtx;
      _14357_encCtx = (input).dtor_encryptionContext;
      if ((AlgorithmSuite.ID.SignatureType(_14356_algID)).is_Some) {
        Dafny.ISequence<byte> _14358_reservedField;
        _14358_reservedField = Materials.__default.EC__PUBLIC__KEY__FIELD;
        if (!(_14357_encCtx).Contains((_14358_reservedField))) {
          res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Could not get materials required for decryption."));
          return res;
        }
        Dafny.ISequence<byte> _14359_encodedVKey;
        _14359_encodedVKey = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(_14357_encCtx,_14358_reservedField);
        Dafny.ISequence<char> _14360_utf8Decoded = Dafny.Sequence<char>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>> _14361_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
        Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>> _out67;
        _out67 = UTF8.__default.Decode(_14359_encodedVKey);
        _14361_valueOrError0 = _out67;
        if ((_14361_valueOrError0).IsFailure()) {
          res = (_14361_valueOrError0).PropagateFailure<Dafny.Aws.Crypto.DecryptMaterialsOutput>();
          return res;
        }
        _14360_utf8Decoded = (_14361_valueOrError0).Extract();
        Dafny.ISequence<byte> _14362_base64Decoded = Dafny.Sequence<byte>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14363_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
        _14363_valueOrError1 = Base64_Compile.__default.Decode(_14360_utf8Decoded);
        if ((_14363_valueOrError1).IsFailure()) {
          res = (_14363_valueOrError1).PropagateFailure<Dafny.Aws.Crypto.DecryptMaterialsOutput>();
          return res;
        }
        _14362_base64Decoded = (_14363_valueOrError1).Extract();
        _14355_vkey = @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_14362_base64Decoded);
      }
      Dafny.Aws.Crypto.DecryptionMaterials _14364_materials;
      _14364_materials = @Dafny.Aws.Crypto.DecryptionMaterials.create((input).dtor_algorithmSuiteId, _14357_encCtx, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), _14355_vkey);
      Dafny.Aws.Crypto.OnDecryptOutput _14365_result = Dafny.Aws.Crypto.OnDecryptOutput.Default();
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>> _14366_valueOrError2 = Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.OnDecryptOutput.Default());
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>> _out68;
      _out68 = ((this).keyring).OnDecrypt(@Dafny.Aws.Crypto.OnDecryptInput.create(_14364_materials, (input).dtor_encryptedDataKeys));
      _14366_valueOrError2 = _out68;
      if ((_14366_valueOrError2).IsFailure()) {
        res = (_14366_valueOrError2).PropagateFailure<Dafny.Aws.Crypto.DecryptMaterialsOutput>();
        return res;
      }
      _14365_result = (_14366_valueOrError2).Extract();
      if ((((_14365_result).dtor_materials).dtor_plaintextDataKey).is_None) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Keyring.OnDecrypt failed to decrypt the plaintext data key."));
        return res;
      }
      res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.DecryptMaterialsOutput.create((_14365_result).dtor_materials));
      return res;
      return res;
    }
    public bool OnEncryptResultValid(Dafny.Aws.Crypto.GetEncryptionMaterialsInput input, Dafny.Aws.Crypto.OnEncryptOutput result)
    {
      return ((((((result).dtor_materials).dtor_plaintextDataKey).is_Some) && (DefaultCMMDef.__default.Serializable((result).dtor_materials))) && (!((((input).dtor_algorithmSuiteId).is_None) || ((AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID(((input).dtor_algorithmSuiteId).dtor_value))).is_Some)) || ((((result).dtor_materials).dtor_encryptionContext).Contains((Materials.__default.EC__PUBLIC__KEY__FIELD))))) && (((System.Func<Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>, bool>)((_source20) => {
        if (_source20.is_None) {
          return (AlgorithmSuite.__default.PolymorphIDToInternalID(((result).dtor_materials).dtor_algorithmSuiteId)) == (888);
        } else {
          Dafny.Aws.Crypto.AlgorithmSuiteId _14367___mcc_h0 = ((Wrappers_Compile.Option_Some<Dafny.Aws.Crypto.AlgorithmSuiteId>)_source20).@value;
          return Dafny.Helpers.Let<Dafny.Aws.Crypto.AlgorithmSuiteId, bool>(_14367___mcc_h0, _pat_let6_0 => Dafny.Helpers.Let<Dafny.Aws.Crypto.AlgorithmSuiteId, bool>(_pat_let6_0, _14368_id => object.Equals(((result).dtor_materials).dtor_algorithmSuiteId, _14368_id)));
        }
      }))((input).dtor_algorithmSuiteId));
    }
    public Dafny.Aws.Crypto.IKeyring _keyring;public Dafny.Aws.Crypto.IKeyring keyring { get {
      return this._keyring;
    } }
  }

  public partial class __default {
    public static bool Serializable(Dafny.Aws.Crypto.EncryptionMaterials mat) {
      return ((new BigInteger(((mat).dtor_encryptedDataKeys).Count)).Sign == 1) && (EncryptionContext.__default.Serializable((mat).dtor_encryptionContext));
    }
  }
} // end of namespace DefaultCMMDef
namespace Serialize_Compile {










  public partial class __default {
    public static Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> SerializeHeaderBody(Streams_Compile.ByteWriter wr, MessageHeader.HeaderBody hb)
    {
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      BigInteger _14369_totalWritten;
      _14369_totalWritten = BigInteger.Zero;
      BigInteger _14370_len;
      BigInteger _out69;
      _out69 = (wr).WriteByte((byte)((hb).dtor_version));
      _14370_len = _out69;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out70;
      _out70 = (wr).WriteByte((byte)((hb).dtor_typ));
      _14370_len = _out70;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out71;
      _out71 = (wr).WriteUInt16((ushort)((hb).dtor_algorithmSuiteID));
      _14370_len = _out71;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out72;
      _out72 = (wr).WriteBytes((hb).dtor_messageID);
      _14370_len = _out72;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14371_valueOrError0 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out73;
      _out73 = Serialize_Compile.__default.SerializeAAD(wr, (hb).dtor_aad);
      _14371_valueOrError0 = _out73;
      if ((_14371_valueOrError0).IsFailure()) {
        ret = (_14371_valueOrError0).PropagateFailure<BigInteger>();
        return ret;
      }
      _14370_len = (_14371_valueOrError0).Extract();
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out74;
      _out74 = Serialize_Compile.__default.SerializeEDKs(wr, (hb).dtor_encryptedDataKeys);
      _14370_len = _out74;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      byte _14372_contentType;
      _14372_contentType = MessageHeader.__default.ContentTypeToUInt8((hb).dtor_contentType);
      BigInteger _out75;
      _out75 = (wr).WriteByte(_14372_contentType);
      _14370_len = _out75;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out76;
      _out76 = (wr).WriteBytes(MessageHeader.__default.Reserved);
      _14370_len = _out76;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out77;
      _out77 = (wr).WriteByte((hb).dtor_ivLength);
      _14370_len = _out77;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      BigInteger _out78;
      _out78 = (wr).WriteUInt32((hb).dtor_frameLength);
      _14370_len = _out78;
      _14369_totalWritten = (_14369_totalWritten) + (_14370_len);
      ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(_14369_totalWritten);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> SerializeHeaderAuthentication(Streams_Compile.ByteWriter wr, MessageHeader.HeaderAuthentication ha)
    {
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      BigInteger _14373_m;
      BigInteger _out79;
      _out79 = (wr).WriteBytes((ha).dtor_iv);
      _14373_m = _out79;
      BigInteger _14374_n;
      BigInteger _out80;
      _out80 = (wr).WriteBytes((ha).dtor_authenticationTag);
      _14374_n = _out80;
      ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success((_14373_m) + (_14374_n));
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> SerializeAAD(Streams_Compile.ByteWriter wr, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> kvPairs)
    {
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      BigInteger _14375_totalWritten;
      _14375_totalWritten = BigInteger.Zero;
      BigInteger _14376_kvPairsLength;
      BigInteger _out81;
      _out81 = EncryptionContext.__default.ComputeLength(kvPairs);
      _14376_kvPairsLength = _out81;
      BigInteger _14377_len;
      BigInteger _out82;
      _out82 = (wr).WriteUInt16((ushort)(_14376_kvPairsLength));
      _14377_len = _out82;
      _14375_totalWritten = (_14375_totalWritten) + (_14377_len);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14378_valueOrError0 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out83;
      _out83 = Serialize_Compile.__default.SerializeKVPairs(wr, kvPairs);
      _14378_valueOrError0 = _out83;
      if ((_14378_valueOrError0).IsFailure()) {
        ret = (_14378_valueOrError0).PropagateFailure<BigInteger>();
        return ret;
      }
      _14377_len = (_14378_valueOrError0).Extract();
      _14375_totalWritten = (_14375_totalWritten) + (_14377_len);
      ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(_14375_totalWritten);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> SerializeKVPairs(Streams_Compile.ByteWriter wr, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      BigInteger _14379_newlyWritten;
      _14379_newlyWritten = BigInteger.Zero;
      if ((new BigInteger((encryptionContext).Count)).Sign == 0) {
        ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(_14379_newlyWritten);
        return ret;
      }
      BigInteger _14380_len;
      BigInteger _out84;
      _out84 = (wr).WriteUInt16((ushort)(encryptionContext).Count);
      _14380_len = _out84;
      _14379_newlyWritten = (_14379_newlyWritten) + (_14380_len);
      Dafny.ISequence<Dafny.ISequence<byte>> _14381_keys;
      Dafny.ISequence<Dafny.ISequence<byte>> _out85;
      _out85 = Sets.__default.SetToOrderedSequence<byte>((encryptionContext).Keys, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _14381_keys = _out85;
      BigInteger _14382_j;
      _14382_j = BigInteger.Zero;
      while ((_14382_j) < (new BigInteger((_14381_keys).Count))) {
        Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14383_valueOrError0 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
        Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out86;
        _out86 = Serialize_Compile.__default.SerializeKVPair(wr, (_14381_keys).Select(_14382_j), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(encryptionContext,(_14381_keys).Select(_14382_j)));
        _14383_valueOrError0 = _out86;
        if ((_14383_valueOrError0).IsFailure()) {
          ret = (_14383_valueOrError0).PropagateFailure<BigInteger>();
          return ret;
        }
        _14380_len = (_14383_valueOrError0).Extract();
        _14379_newlyWritten = (_14379_newlyWritten) + (_14380_len);
        _14382_j = (_14382_j) + (BigInteger.One);
      }
      ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(_14379_newlyWritten);
      return ret;
      return ret;
    }
    public static Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> SerializeKVPair(Streams_Compile.ByteWriter wr, Dafny.ISequence<byte> k, Dafny.ISequence<byte> v)
    {
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> ret = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      BigInteger _14384_newlyWritten;
      _14384_newlyWritten = BigInteger.Zero;
      BigInteger _14385_len;
      BigInteger _out87;
      _out87 = (wr).WriteUInt16((ushort)(k).Count);
      _14385_len = _out87;
      _14384_newlyWritten = (_14384_newlyWritten) + (_14385_len);
      BigInteger _out88;
      _out88 = (wr).WriteBytes(k);
      _14385_len = _out88;
      _14384_newlyWritten = (_14384_newlyWritten) + (_14385_len);
      BigInteger _out89;
      _out89 = (wr).WriteUInt16((ushort)(v).Count);
      _14385_len = _out89;
      _14384_newlyWritten = (_14384_newlyWritten) + (_14385_len);
      BigInteger _out90;
      _out90 = (wr).WriteBytes(v);
      _14385_len = _out90;
      _14384_newlyWritten = (_14384_newlyWritten) + (_14385_len);
      ret = @Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(_14384_newlyWritten);
      return ret;
      return ret;
    }
    public static BigInteger SerializeEDKs(Streams_Compile.ByteWriter wr, MessageHeader.EncryptedDataKeys encryptedDataKeys)
    {
      BigInteger ret = BigInteger.Zero;
      BigInteger _14386_totalWritten;
      _14386_totalWritten = BigInteger.Zero;
      BigInteger _14387_len;
      BigInteger _out91;
      _out91 = (wr).WriteUInt16((ushort)((encryptedDataKeys).dtor_entries).Count);
      _14387_len = _out91;
      _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
      BigInteger _14388_j;
      _14388_j = BigInteger.Zero;
      while ((_14388_j) < (new BigInteger(((encryptedDataKeys).dtor_entries).Count))) {
        Dafny.Aws.Crypto.EncryptedDataKey _14389_entry;
        _14389_entry = ((encryptedDataKeys).dtor_entries).Select(_14388_j);
        BigInteger _out92;
        _out92 = (wr).WriteUInt16((ushort)((_14389_entry).dtor_keyProviderId).Count);
        _14387_len = _out92;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        BigInteger _out93;
        _out93 = (wr).WriteBytes((_14389_entry).dtor_keyProviderId);
        _14387_len = _out93;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        BigInteger _out94;
        _out94 = (wr).WriteUInt16((ushort)((_14389_entry).dtor_keyProviderInfo).Count);
        _14387_len = _out94;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        BigInteger _out95;
        _out95 = (wr).WriteBytes((_14389_entry).dtor_keyProviderInfo);
        _14387_len = _out95;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        BigInteger _out96;
        _out96 = (wr).WriteUInt16((ushort)((_14389_entry).dtor_ciphertext).Count);
        _14387_len = _out96;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        BigInteger _out97;
        _out97 = (wr).WriteBytes((_14389_entry).dtor_ciphertext);
        _14387_len = _out97;
        _14386_totalWritten = (_14386_totalWritten) + (_14387_len);
        _14388_j = (_14388_j) + (BigInteger.One);
      }
      ret = _14386_totalWritten;
      return ret;
      return ret;
    }
  }
} // end of namespace Serialize_Compile
namespace RawAESKeyringDef {















  public partial class RawAESKeyring : Dafny.Aws.Crypto.IKeyring {
    public RawAESKeyring() {
      this._keyNamespace = UTF8.ValidUTF8Bytes.Default();
      this._keyName = UTF8.ValidUTF8Bytes.Default();
      this._wrappingKey = Dafny.Sequence<byte>.Empty;
      this._wrappingAlgorithm = EncryptionSuites.EncryptionSuite.Default();
    }
    public bool Valid() {
      return ((((new BigInteger(((this).wrappingKey).Count)) == (new BigInteger(((this).wrappingAlgorithm).dtor_keyLen))) && ((RawAESKeyringDef.__default.VALID__ALGORITHMS).Contains(((this).wrappingAlgorithm)))) && (((this).wrappingAlgorithm).Valid())) && ((new BigInteger(((this).keyNamespace).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT));
    }
    public bool ValidEncryptionMaterials(Dafny.Aws.Crypto.EncryptionMaterials mat) {
      return ((!((AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((mat).dtor_algorithmSuiteId))).is_Some) || (((mat).dtor_signingKey).is_Some)) && (!(((mat).dtor_plaintextDataKey).is_Some) || (AlgorithmSuite.ID.ValidPlaintextDataKey(AlgorithmSuite.__default.PolymorphIDToInternalID((mat).dtor_algorithmSuiteId), ((mat).dtor_plaintextDataKey).dtor_value)))) && (!(((mat).dtor_plaintextDataKey).is_None) || ((new BigInteger(((mat).dtor_encryptedDataKeys).Count)).Sign == 0));
    }
    public void __ctor(Dafny.ISequence<byte> @namespace, Dafny.ISequence<byte> name, Dafny.ISequence<byte> key, EncryptionSuites.EncryptionSuite wrappingAlg)
    {
      (this)._keyNamespace = @namespace;
      (this)._keyName = name;
      (this)._wrappingKey = key;
      (this)._wrappingAlgorithm = wrappingAlg;
    }
    public Dafny.ISequence<byte> SerializeProviderInfo(Dafny.ISequence<byte> iv) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat((this).keyName, Dafny.Sequence<byte>.FromElements(0, 0, 0, (byte)((((this).wrappingAlgorithm).dtor_tagLen) * (8)))), Dafny.Sequence<byte>.FromElements(0, 0, 0, ((this).wrappingAlgorithm).dtor_ivLen)), iv);
    }
    public Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>> OnEncrypt(Dafny.Aws.Crypto.OnEncryptInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.OnEncryptOutput.Default());
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14390_valueOrError0 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _14390_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((this).Valid(), Dafny.Sequence<char>.FromString("Keyring in invalid state"));
      if ((_14390_valueOrError0).IsFailure()) {
        res = (_14390_valueOrError0).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
        return res;
      }
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14391_valueOrError1 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _14391_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((this).ValidEncryptionMaterials((input).dtor_materials), Dafny.Sequence<char>.FromString("input encryption materials invalid"));
      if ((_14391_valueOrError1).IsFailure()) {
        res = (_14391_valueOrError1).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
        return res;
      }
      bool _14392_valid;
      bool _out98;
      _out98 = EncryptionContext.__default.CheckSerializable(((input).dtor_materials).dtor_encryptionContext);
      _14392_valid = _out98;
      if (!(_14392_valid)) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Unable to serialize encryption context"));
        return res;
      }
      Dafny.Aws.Crypto.EncryptionMaterials _14393_materialsWithDataKey;
      _14393_materialsWithDataKey = (input).dtor_materials;
      if (((_14393_materialsWithDataKey).dtor_plaintextDataKey).is_None) {
        Dafny.ISequence<byte> _14394_k = Dafny.Sequence<byte>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14395_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out99;
        _out99 = Random_Compile.__default.GenerateBytes((int)(AlgorithmSuite.ID.KeyLength(AlgorithmSuite.__default.PolymorphIDToInternalID(((input).dtor_materials).dtor_algorithmSuiteId))));
        _14395_valueOrError2 = _out99;
        if ((_14395_valueOrError2).IsFailure()) {
          res = (_14395_valueOrError2).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
          return res;
        }
        _14394_k = (_14395_valueOrError2).Extract();
        _14393_materialsWithDataKey = @Dafny.Aws.Crypto.EncryptionMaterials.create((_14393_materialsWithDataKey).dtor_algorithmSuiteId, (_14393_materialsWithDataKey).dtor_encryptionContext, Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromElements(), @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_14394_k), (_14393_materialsWithDataKey).dtor_signingKey);
      }
      Dafny.ISequence<byte> _14396_iv = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14397_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out100;
      _out100 = Random_Compile.__default.GenerateBytes((int)(((this).wrappingAlgorithm).dtor_ivLen));
      _14397_valueOrError3 = _out100;
      if ((_14397_valueOrError3).IsFailure()) {
        res = (_14397_valueOrError3).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
        return res;
      }
      _14396_iv = (_14397_valueOrError3).Extract();
      Dafny.ISequence<byte> _14398_providerInfo;
      _14398_providerInfo = (this).SerializeProviderInfo(_14396_iv);
      Streams_Compile.ByteWriter _14399_wr;
      Streams_Compile.ByteWriter _nw7 = new Streams_Compile.ByteWriter();
      _nw7.__ctor();
      _14399_wr = _nw7;
      BigInteger _14400___v0 = BigInteger.Zero;
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14401_valueOrError4 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out101;
      _out101 = Serialize_Compile.__default.SerializeKVPairs(_14399_wr, ((input).dtor_materials).dtor_encryptionContext);
      _14401_valueOrError4 = _out101;
      if ((_14401_valueOrError4).IsFailure()) {
        res = (_14401_valueOrError4).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
        return res;
      }
      _14400___v0 = (_14401_valueOrError4).Extract();
      Dafny.ISequence<byte> _14402_aad;
      _14402_aad = (_14399_wr).GetDataWritten();
      AESEncryption.EncryptionOutput _14403_encryptResult = AESEncryption.EncryptionOutput.Default();
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _14404_valueOrError5 = Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>>.Default(AESEncryption.EncryptionOutput.Default());
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _out102;
      _out102 = AESEncryption.__default.AESEncrypt((this).wrappingAlgorithm, _14396_iv, (this).wrappingKey, ((_14393_materialsWithDataKey).dtor_plaintextDataKey).dtor_value, _14402_aad);
      _14404_valueOrError5 = _out102;
      if ((_14404_valueOrError5).IsFailure()) {
        res = (_14404_valueOrError5).PropagateFailure<Dafny.Aws.Crypto.OnEncryptOutput>();
        return res;
      }
      _14403_encryptResult = (_14404_valueOrError5).Extract();
      Dafny.ISequence<byte> _14405_encryptedKey;
      _14405_encryptedKey = RawAESKeyringDef.__default.SerializeEDKCiphertext(_14403_encryptResult);
      if ((StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT) <= (new BigInteger((_14398_providerInfo).Count))) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Serialized provider info too long."));
        return res;
      }
      if ((StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT) <= (new BigInteger((_14405_encryptedKey).Count))) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Encrypted data key too long."));
        return res;
      }
      Dafny.Aws.Crypto.EncryptedDataKey _14406_edk;
      _14406_edk = @Dafny.Aws.Crypto.EncryptedDataKey.create((this).keyNamespace, _14398_providerInfo, _14405_encryptedKey);
      Dafny.ISequence<Dafny.Aws.Crypto.EncryptedDataKey> _14407_edks;
      _14407_edks = Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.Concat((_14393_materialsWithDataKey).dtor_encryptedDataKeys, Dafny.Sequence<Dafny.Aws.Crypto.EncryptedDataKey>.FromElements(_14406_edk));
      Dafny.Aws.Crypto.EncryptionMaterials _14408_r;
      _14408_r = @Dafny.Aws.Crypto.EncryptionMaterials.create((_14393_materialsWithDataKey).dtor_algorithmSuiteId, (_14393_materialsWithDataKey).dtor_encryptionContext, _14407_edks, (_14393_materialsWithDataKey).dtor_plaintextDataKey, (_14393_materialsWithDataKey).dtor_signingKey);
      res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnEncryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.OnEncryptOutput.create(_14408_r));
      return res;
    }
    public Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>> OnDecrypt(Dafny.Aws.Crypto.OnDecryptInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.OnDecryptOutput.Default());
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14409_valueOrError0 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _14409_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((this).Valid(), Dafny.Sequence<char>.FromString("Keyring in invalid state"));
      if ((_14409_valueOrError0).IsFailure()) {
        res = (_14409_valueOrError0).PropagateFailure<Dafny.Aws.Crypto.OnDecryptOutput>();
        return res;
      }
      if ((((input).dtor_materials).dtor_plaintextDataKey).is_Some) {
        res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.OnDecryptOutput.create((input).dtor_materials));
        return res;
      }
      BigInteger _14410_i;
      _14410_i = BigInteger.Zero;
      while ((_14410_i) < (new BigInteger(((input).dtor_encryptedDataKeys).Count))) {
        if ((this).ShouldDecryptEDK(((input).dtor_encryptedDataKeys).Select(_14410_i))) {
          bool _14411_valid;
          bool _out103;
          _out103 = EncryptionContext.__default.CheckSerializable(((input).dtor_materials).dtor_encryptionContext);
          _14411_valid = _out103;
          if (!(_14411_valid)) {
            res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Unable to serialize encryption context"));
            return res;
          }
          Streams_Compile.ByteWriter _14412_wr;
          Streams_Compile.ByteWriter _nw8 = new Streams_Compile.ByteWriter();
          _nw8.__ctor();
          _14412_wr = _nw8;
          BigInteger _14413___v1 = BigInteger.Zero;
          Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14414_valueOrError1 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
          Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out104;
          _out104 = Serialize_Compile.__default.SerializeKVPairs(_14412_wr, ((input).dtor_materials).dtor_encryptionContext);
          _14414_valueOrError1 = _out104;
          if ((_14414_valueOrError1).IsFailure()) {
            res = (_14414_valueOrError1).PropagateFailure<Dafny.Aws.Crypto.OnDecryptOutput>();
            return res;
          }
          _14413___v1 = (_14414_valueOrError1).Extract();
          Dafny.ISequence<byte> _14415_aad;
          _14415_aad = (_14412_wr).GetDataWritten();
          Dafny.ISequence<byte> _14416_iv;
          _14416_iv = (this).GetIvFromProvInfo((((input).dtor_encryptedDataKeys).Select(_14410_i)).dtor_keyProviderInfo);
          AESEncryption.EncryptionOutput _14417_encryptionOutput;
          _14417_encryptionOutput = RawAESKeyringDef.__default.DeserializeEDKCiphertext((((input).dtor_encryptedDataKeys).Select(_14410_i)).dtor_ciphertext, new BigInteger(((this).wrappingAlgorithm).dtor_tagLen));
          Dafny.ISequence<byte> _14418_ptKey = Dafny.Sequence<byte>.Empty;
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14419_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out105;
          _out105 = AESEncryption.__default.AESDecrypt((this).wrappingAlgorithm, (this).wrappingKey, (_14417_encryptionOutput).dtor_cipherText, (_14417_encryptionOutput).dtor_authTag, _14416_iv, _14415_aad);
          _14419_valueOrError2 = _out105;
          if ((_14419_valueOrError2).IsFailure()) {
            res = (_14419_valueOrError2).PropagateFailure<Dafny.Aws.Crypto.OnDecryptOutput>();
            return res;
          }
          _14418_ptKey = (_14419_valueOrError2).Extract();
          if (AlgorithmSuite.ID.ValidPlaintextDataKey(AlgorithmSuite.__default.PolymorphIDToInternalID(((input).dtor_materials).dtor_algorithmSuiteId), _14418_ptKey)) {
            Dafny.Aws.Crypto.DecryptionMaterials _14420_r;
            _14420_r = @Dafny.Aws.Crypto.DecryptionMaterials.create(((input).dtor_materials).dtor_algorithmSuiteId, ((input).dtor_materials).dtor_encryptionContext, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_14418_ptKey), ((input).dtor_materials).dtor_verificationKey);
            res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.OnDecryptOutput.create(_14420_r));
            return res;
          } else {
            res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Decryption failed: bad datakey length."));
            return res;
          }
        }
        _14410_i = (_14410_i) + (BigInteger.One);
      }
      res = @Wrappers_Compile.Result<Dafny.Aws.Crypto.OnDecryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Crypto.OnDecryptOutput.create((input).dtor_materials));
      return res;
      return res;
    }
    public bool ShouldDecryptEDK(Dafny.Aws.Crypto.EncryptedDataKey edk) {
      return ((((edk).dtor_keyProviderId).Equals(((this).keyNamespace))) && ((this).ValidProviderInfo((edk).dtor_keyProviderInfo))) && ((new BigInteger(((this).wrappingAlgorithm).dtor_tagLen)) <= (new BigInteger(((edk).dtor_ciphertext).Count)));
    }
    public bool ValidProviderInfo(Dafny.ISequence<byte> info) {
      return ((((((new BigInteger((info).Count)) == ((((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)) + (RawAESKeyringDef.__default.IV__LEN__LEN)) + (new BigInteger(((this).wrappingAlgorithm).dtor_ivLen)))) && (((info).Subsequence(BigInteger.Zero, new BigInteger(((this).keyName).Count))).Equals(((this).keyName)))) && ((StandardLibrary_mUInt_Compile.__default.SeqToUInt32((info).Subsequence(new BigInteger(((this).keyName).Count), (new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)))) == (128U))) && ((StandardLibrary_mUInt_Compile.__default.SeqToUInt32((info).Subsequence(new BigInteger(((this).keyName).Count), (new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)))) == (((uint)(((this).wrappingAlgorithm).dtor_tagLen)) * (8U)))) && ((StandardLibrary_mUInt_Compile.__default.SeqToUInt32((info).Subsequence((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN), ((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)) + (RawAESKeyringDef.__default.IV__LEN__LEN)))) == ((uint)(((this).wrappingAlgorithm).dtor_ivLen)))) && ((StandardLibrary_mUInt_Compile.__default.SeqToUInt32((info).Subsequence((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN), ((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)) + (RawAESKeyringDef.__default.IV__LEN__LEN)))) == (12U));
    }
    public Dafny.ISequence<byte> GetIvFromProvInfo(Dafny.ISequence<byte> info) {
      return (info).Drop(((new BigInteger(((this).keyName).Count)) + (RawAESKeyringDef.__default.AUTH__TAG__LEN__LEN)) + (RawAESKeyringDef.__default.IV__LEN__LEN));
    }
    public Dafny.ISequence<byte> _keyNamespace;public Dafny.ISequence<byte> keyNamespace { get {
      return this._keyNamespace;
    } }
    public Dafny.ISequence<byte> _keyName;public Dafny.ISequence<byte> keyName { get {
      return this._keyName;
    } }
    public Dafny.ISequence<byte> _wrappingKey;public Dafny.ISequence<byte> wrappingKey { get {
      return this._wrappingKey;
    } }
    public EncryptionSuites.EncryptionSuite _wrappingAlgorithm;public EncryptionSuites.EncryptionSuite wrappingAlgorithm { get {
      return this._wrappingAlgorithm;
    } }
  }

  public partial class __default {
    public static AESEncryption.EncryptionOutput DeserializeEDKCiphertext(Dafny.ISequence<byte> ciphertext, BigInteger tagLen)
    {
      BigInteger _14421_encryptedKeyLength = (new BigInteger((ciphertext).Count)) - (tagLen);
      return @AESEncryption.EncryptionOutput.create((ciphertext).Take(_14421_encryptedKeyLength), (ciphertext).Drop(_14421_encryptedKeyLength));
    }
    public static Dafny.ISequence<byte> SerializeEDKCiphertext(AESEncryption.EncryptionOutput encOutput) {
      return Dafny.Sequence<byte>.Concat((encOutput).dtor_cipherText, (encOutput).dtor_authTag);
    }
    public static Dafny.ISet<EncryptionSuites.EncryptionSuite> VALID__ALGORITHMS { get {
      return Dafny.Set<EncryptionSuites.EncryptionSuite>.FromElements(EncryptionSuites.__default.AES__GCM__128, EncryptionSuites.__default.AES__GCM__192, EncryptionSuites.__default.AES__GCM__256);
    } }
    public static BigInteger AUTH__TAG__LEN__LEN { get {
      return new BigInteger(4);
    } }
    public static BigInteger IV__LEN__LEN { get {
      return new BigInteger(4);
    } }
  }
} // end of namespace RawAESKeyringDef
namespace Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient {










  public partial class AwsCryptographicMaterialProvidersClient : Dafny.Aws.Crypto.IAwsCryptographicMaterialsProviderClient {
    public AwsCryptographicMaterialProvidersClient() {
    }
    public void __ctor()
    {
    }
    public Dafny.Aws.Crypto.IKeyring CreateRawAesKeyring(Dafny.Aws.Crypto.CreateRawAesKeyringInput input)
    {
      Dafny.Aws.Crypto.IKeyring res = default(Dafny.Aws.Crypto.IKeyring);
      EncryptionSuites.EncryptionSuite _14422_wrappingAlg = EncryptionSuites.EncryptionSuite.Default();
      if (object.Equals((input).dtor_wrappingAlg, @Dafny.Aws.Crypto.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16())) {
        _14422_wrappingAlg = EncryptionSuites.__default.AES__GCM__128;
      } else if (object.Equals((input).dtor_wrappingAlg, @Dafny.Aws.Crypto.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16())) {
        _14422_wrappingAlg = EncryptionSuites.__default.AES__GCM__192;
      } else {
        _14422_wrappingAlg = EncryptionSuites.__default.AES__GCM__256;
      }
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14423_namespaceRes;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out106;
      _out106 = UTF8.__default.Encode((input).dtor_keyNamespace);
      _14423_namespaceRes = _out106;
      Dafny.ISequence<byte> _14424_namespace = UTF8.ValidUTF8Bytes.Default();
      if ((_14423_namespaceRes).is_Success) {
        _14424_namespace = (_14423_namespaceRes).dtor_value;
      }
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14425_nameRes;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out107;
      _out107 = UTF8.__default.Encode((input).dtor_keyName);
      _14425_nameRes = _out107;
      Dafny.ISequence<byte> _14426_name = UTF8.ValidUTF8Bytes.Default();
      if ((_14425_nameRes).is_Success) {
        _14426_name = (_14425_nameRes).dtor_value;
      }
      if (!((new BigInteger((_14424_namespace).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/AwsCryptographicMaterialProviders.dfy(55,6): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((((new BigInteger(((input).dtor_wrappingKey).Count)) == (new BigInteger(16))) || ((new BigInteger(((input).dtor_wrappingKey).Count)) == (new BigInteger(24)))) || ((new BigInteger(((input).dtor_wrappingKey).Count)) == (new BigInteger(32))))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/AwsCryptographicMaterialProviders.dfy(56,6): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger(((input).dtor_wrappingKey).Count)) == (new BigInteger((_14422_wrappingAlg).dtor_keyLen)))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/AwsCryptographicMaterialProviders.dfy(57,6): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      RawAESKeyringDef.RawAESKeyring _nw9 = new RawAESKeyringDef.RawAESKeyring();
      _nw9.__ctor(_14424_namespace, _14426_name, (input).dtor_wrappingKey, _14422_wrappingAlg);
      res = _nw9;
      return res;
      return res;
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(Dafny.Aws.Crypto.CreateDefaultCryptographicMaterialsManagerInput input)
    {
      Dafny.Aws.Crypto.ICryptographicMaterialsManager res = default(Dafny.Aws.Crypto.ICryptographicMaterialsManager);
      DefaultCMMDef.DefaultCMM _nw10 = new DefaultCMMDef.DefaultCMM();
      _nw10.OfKeyring((input).dtor_keyring);
      res = _nw10;
      return res;
      return res;
    }
  }

} // end of namespace Dafny.Aws.Crypto.AwsCryptographicMaterialProvidersClient
namespace MessageBody_Compile {











  public abstract class BodyAADContent {
    public BodyAADContent() { }
    private static readonly BodyAADContent theDefault = create_AADRegularFrame();
    public static BodyAADContent Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageBody_Compile.BodyAADContent> _TYPE = new Dafny.TypeDescriptor<MessageBody_Compile.BodyAADContent>(MessageBody_Compile.BodyAADContent.Default());
    public static Dafny.TypeDescriptor<MessageBody_Compile.BodyAADContent> _TypeDescriptor() {
      return _TYPE;
    }
    public static BodyAADContent create_AADRegularFrame() {
      return new BodyAADContent_AADRegularFrame();
    }
    public static BodyAADContent create_AADFinalFrame() {
      return new BodyAADContent_AADFinalFrame();
    }
    public static BodyAADContent create_AADSingleBlock() {
      return new BodyAADContent_AADSingleBlock();
    }
    public bool is_AADRegularFrame { get { return this is BodyAADContent_AADRegularFrame; } }
    public bool is_AADFinalFrame { get { return this is BodyAADContent_AADFinalFrame; } }
    public bool is_AADSingleBlock { get { return this is BodyAADContent_AADSingleBlock; } }
    public static System.Collections.Generic.IEnumerable<BodyAADContent> AllSingletonConstructors {
      get {
        yield return BodyAADContent.create_AADRegularFrame();
        yield return BodyAADContent.create_AADFinalFrame();
        yield return BodyAADContent.create_AADSingleBlock();
      }
    }
  }
  public class BodyAADContent_AADRegularFrame : BodyAADContent {
    public BodyAADContent_AADRegularFrame() {
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.BodyAADContent_AADRegularFrame;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.BodyAADContent.AADRegularFrame";
      return s;
    }
  }
  public class BodyAADContent_AADFinalFrame : BodyAADContent {
    public BodyAADContent_AADFinalFrame() {
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.BodyAADContent_AADFinalFrame;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.BodyAADContent.AADFinalFrame";
      return s;
    }
  }
  public class BodyAADContent_AADSingleBlock : BodyAADContent {
    public BodyAADContent_AADSingleBlock() {
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.BodyAADContent_AADSingleBlock;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.BodyAADContent.AADSingleBlock";
      return s;
    }
  }

  public abstract class Frame {
    public Frame() { }
    private static readonly Frame theDefault = create_RegularFrame(0, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static Frame Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageBody_Compile.Frame> _TYPE = new Dafny.TypeDescriptor<MessageBody_Compile.Frame>(MessageBody_Compile.Frame.Default());
    public static Dafny.TypeDescriptor<MessageBody_Compile.Frame> _TypeDescriptor() {
      return _TYPE;
    }
    public static Frame create_RegularFrame(uint seqNum, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> encContent, Dafny.ISequence<byte> authTag) {
      return new Frame_RegularFrame(seqNum, iv, encContent, authTag);
    }
    public static Frame create_FinalFrame(uint seqNum, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> encContent, Dafny.ISequence<byte> authTag) {
      return new Frame_FinalFrame(seqNum, iv, encContent, authTag);
    }
    public bool is_RegularFrame { get { return this is Frame_RegularFrame; } }
    public bool is_FinalFrame { get { return this is Frame_FinalFrame; } }
    public uint dtor_seqNum {
      get {
        var d = this;
        if (d is Frame_RegularFrame) { return ((Frame_RegularFrame)d).seqNum; }
        return ((Frame_FinalFrame)d).seqNum; 
      }
    }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        var d = this;
        if (d is Frame_RegularFrame) { return ((Frame_RegularFrame)d).iv; }
        return ((Frame_FinalFrame)d).iv; 
      }
    }
    public Dafny.ISequence<byte> dtor_encContent {
      get {
        var d = this;
        if (d is Frame_RegularFrame) { return ((Frame_RegularFrame)d).encContent; }
        return ((Frame_FinalFrame)d).encContent; 
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        var d = this;
        if (d is Frame_RegularFrame) { return ((Frame_RegularFrame)d).authTag; }
        return ((Frame_FinalFrame)d).authTag; 
      }
    }
  }
  public class Frame_RegularFrame : Frame {
    public readonly uint seqNum;
    public readonly Dafny.ISequence<byte> iv;
    public readonly Dafny.ISequence<byte> encContent;
    public readonly Dafny.ISequence<byte> authTag;
    public Frame_RegularFrame(uint seqNum, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> encContent, Dafny.ISequence<byte> authTag) {
      this.seqNum = seqNum;
      this.iv = iv;
      this.encContent = encContent;
      this.authTag = authTag;
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.Frame_RegularFrame;
      return oth != null && this.seqNum == oth.seqNum && object.Equals(this.iv, oth.iv) && object.Equals(this.encContent, oth.encContent) && object.Equals(this.authTag, oth.authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.seqNum));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encContent));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.Frame.RegularFrame";
      s += "(";
      s += Dafny.Helpers.ToString(this.seqNum);
      s += ", ";
      s += Dafny.Helpers.ToString(this.iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encContent);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authTag);
      s += ")";
      return s;
    }
  }
  public class Frame_FinalFrame : Frame {
    public readonly uint seqNum;
    public readonly Dafny.ISequence<byte> iv;
    public readonly Dafny.ISequence<byte> encContent;
    public readonly Dafny.ISequence<byte> authTag;
    public Frame_FinalFrame(uint seqNum, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> encContent, Dafny.ISequence<byte> authTag) {
      this.seqNum = seqNum;
      this.iv = iv;
      this.encContent = encContent;
      this.authTag = authTag;
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.Frame_FinalFrame;
      return oth != null && this.seqNum == oth.seqNum && object.Equals(this.iv, oth.iv) && object.Equals(this.encContent, oth.encContent) && object.Equals(this.authTag, oth.authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.seqNum));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encContent));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.Frame.FinalFrame";
      s += "(";
      s += Dafny.Helpers.ToString(this.seqNum);
      s += ", ";
      s += Dafny.Helpers.ToString(this.iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encContent);
      s += ", ";
      s += Dafny.Helpers.ToString(this.authTag);
      s += ")";
      return s;
    }
  }

  public class SeqWithGhostFrames {
    public readonly Dafny.ISequence<byte> sequence;
    public SeqWithGhostFrames(Dafny.ISequence<byte> sequence) {
      this.sequence = sequence;
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.SeqWithGhostFrames;
      return oth != null && object.Equals(this.sequence, oth.sequence);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.sequence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.SeqWithGhostFrames.SeqWithGhostFrames";
      s += "(";
      s += Dafny.Helpers.ToString(this.sequence);
      s += ")";
      return s;
    }
    private static readonly SeqWithGhostFrames theDefault = create(Dafny.Sequence<byte>.Empty);
    public static SeqWithGhostFrames Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageBody_Compile.SeqWithGhostFrames> _TYPE = new Dafny.TypeDescriptor<MessageBody_Compile.SeqWithGhostFrames>(MessageBody_Compile.SeqWithGhostFrames.Default());
    public static Dafny.TypeDescriptor<MessageBody_Compile.SeqWithGhostFrames> _TypeDescriptor() {
      return _TYPE;
    }
    public static SeqWithGhostFrames create(Dafny.ISequence<byte> sequence) {
      return new SeqWithGhostFrames(sequence);
    }
    public bool is_SeqWithGhostFrames { get { return true; } }
    public Dafny.ISequence<byte> dtor_sequence {
      get {
        return this.sequence;
      }
    }
  }

  public class FrameWithGhostSeq {
    public readonly MessageBody_Compile.Frame frame;
    public FrameWithGhostSeq(MessageBody_Compile.Frame frame) {
      this.frame = frame;
    }
    public override bool Equals(object other) {
      var oth = other as MessageBody_Compile.FrameWithGhostSeq;
      return oth != null && object.Equals(this.frame, oth.frame);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frame));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MessageBody_Compile.FrameWithGhostSeq.FrameWithGhostSeq";
      s += "(";
      s += Dafny.Helpers.ToString(this.frame);
      s += ")";
      return s;
    }
    private static readonly FrameWithGhostSeq theDefault = create(MessageBody_Compile.Frame.Default());
    public static FrameWithGhostSeq Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<MessageBody_Compile.FrameWithGhostSeq> _TYPE = new Dafny.TypeDescriptor<MessageBody_Compile.FrameWithGhostSeq>(MessageBody_Compile.FrameWithGhostSeq.Default());
    public static Dafny.TypeDescriptor<MessageBody_Compile.FrameWithGhostSeq> _TypeDescriptor() {
      return _TYPE;
    }
    public static FrameWithGhostSeq create(MessageBody_Compile.Frame frame) {
      return new FrameWithGhostSeq(frame);
    }
    public bool is_FrameWithGhostSeq { get { return true; } }
    public MessageBody_Compile.Frame dtor_frame {
      get {
        return this.frame;
      }
    }
  }

  public partial class __default {
    public static Dafny.ISequence<char> BodyAADContentTypeString(MessageBody_Compile.BodyAADContent bc) {
      MessageBody_Compile.BodyAADContent _source21 = bc;
      if (_source21.is_AADRegularFrame) {
        return MessageBody_Compile.__default.BODY__AAD__CONTENT__REGULAR__FRAME;
      } else if (_source21.is_AADFinalFrame) {
        return MessageBody_Compile.__default.BODY__AAD__CONTENT__FINAL__FRAME;
      } else {
        return MessageBody_Compile.__default.BODY__AAD__CONTENT__SINGLE__BLOCK;
      }
    }
    public static Dafny.ISequence<byte> IVSeq(ushort algorithmSuiteID, uint sequenceNumber)
    {
      return Dafny.Sequence<byte>.Concat(((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim9 = (AlgorithmSuite.ID.IVLength(algorithmSuiteID)) - (new BigInteger(4));
        var arr9 = new byte[Dafny.Helpers.ToIntChecked(dim9,"C# array size must not be larger than max 32-bit int")];
        for (int i9 = 0; i9 < dim9; i9++) {
          var _14427___v0 = (BigInteger) i9;
          arr9[(int)(_14427___v0)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr9);
      }))(), StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(sequenceNumber));
    }
    public static Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>> EncryptMessageBody(Dafny.ISequence<byte> plaintext, BigInteger frameLength, Dafny.ISequence<byte> messageID, Dafny.ISequence<byte> key, ushort algorithmSuiteID)
    {
      Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>> result = Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>>.Default(MessageBody_Compile.SeqWithGhostFrames.Default());
      Dafny.ISequence<byte> _14428_body;
      _14428_body = Dafny.Sequence<byte>.FromElements();
      BigInteger _14429_n;
      uint _14430_sequenceNumber;
      BigInteger _rhs2 = BigInteger.Zero;
      uint _rhs3 = MessageBody_Compile.__default.START__SEQUENCE__NUMBER;
      _14429_n = _rhs2;
      _14430_sequenceNumber = _rhs3;
      while (((_14429_n) + (frameLength)) < (new BigInteger((plaintext).Count))) {
        if ((_14430_sequenceNumber) == (MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER)) {
          result = @Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("too many frames"));
          return result;
        }
        Dafny.ISequence<byte> _14431_plaintextFrame;
        _14431_plaintextFrame = (plaintext).Subsequence(_14429_n, (_14429_n) + (frameLength));
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14432_regularFrame;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out108;
        _out108 = MessageBody_Compile.__default.EncryptRegularFrame(algorithmSuiteID, key, messageID, _14431_plaintextFrame, _14430_sequenceNumber);
        _14432_regularFrame = _out108;
        if ((_14432_regularFrame).IsFailure()) {
          result = (_14432_regularFrame).PropagateFailure<MessageBody_Compile.SeqWithGhostFrames>();
          return result;
        }
        _14428_body = Dafny.Sequence<byte>.Concat(_14428_body, (_14432_regularFrame).Extract());
        BigInteger _rhs4 = (_14429_n) + (frameLength);
        uint _rhs5 = (_14430_sequenceNumber) + (1U);
        _14429_n = _rhs4;
        _14430_sequenceNumber = _rhs5;
      }
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14433_finalFrameResult;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out109;
      _out109 = MessageBody_Compile.__default.EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, (plaintext).Drop(_14429_n), _14430_sequenceNumber);
      _14433_finalFrameResult = _out109;
      if ((_14433_finalFrameResult).IsFailure()) {
        result = (_14433_finalFrameResult).PropagateFailure<MessageBody_Compile.SeqWithGhostFrames>();
        return result;
      }
      Dafny.ISequence<byte> _14434_finalFrameSequence;
      _14434_finalFrameSequence = (_14433_finalFrameResult).Extract();
      _14428_body = Dafny.Sequence<byte>.Concat(_14428_body, _14434_finalFrameSequence);
      result = @Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>>.create_Success(@MessageBody_Compile.SeqWithGhostFrames.create(_14428_body));
      return result;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> EncryptRegularFrame(ushort algorithmSuiteID, Dafny.ISequence<byte> key, Dafny.ISequence<byte> messageID, Dafny.ISequence<byte> plaintext, uint sequenceNumber)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14435_seqNumSeq;
      _14435_seqNumSeq = StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(sequenceNumber);
      Dafny.ISequence<byte> _14436_unauthenticatedFrame;
      _14436_unauthenticatedFrame = _14435_seqNumSeq;
      Dafny.ISequence<byte> _14437_iv;
      _14437_iv = MessageBody_Compile.__default.IVSeq(algorithmSuiteID, sequenceNumber);
      Dafny.ISequence<byte> _14438_aad;
      Dafny.ISequence<byte> _out110;
      _out110 = MessageBody_Compile.__default.BodyAAD(messageID, @MessageBody_Compile.BodyAADContent.create_AADRegularFrame(), sequenceNumber, (ulong)(plaintext).LongCount);
      _14438_aad = _out110;
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _14439_encryptionOutputResult;
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _out111;
      _out111 = AESEncryption.__default.AESEncrypt(AlgorithmSuite.ID.EncryptionSuite(algorithmSuiteID), _14437_iv, key, plaintext, _14438_aad);
      _14439_encryptionOutputResult = _out111;
      if ((_14439_encryptionOutputResult).IsFailure()) {
        res = (_14439_encryptionOutputResult).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      AESEncryption.EncryptionOutput _14440_encryptionOutput;
      _14440_encryptionOutput = (_14439_encryptionOutputResult).Extract();
      _14436_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(_14436_unauthenticatedFrame, _14437_iv);
      _14436_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_14436_unauthenticatedFrame, (_14440_encryptionOutput).dtor_cipherText), (_14440_encryptionOutput).dtor_authTag);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _rhs6 = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14436_unauthenticatedFrame);
      res = _rhs6;
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> EncryptFinalFrame(ushort algorithmSuiteID, Dafny.ISequence<byte> key, BigInteger frameLength, Dafny.ISequence<byte> messageID, Dafny.ISequence<byte> plaintext, uint sequenceNumber)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14441_unauthenticatedFrame;
      _14441_unauthenticatedFrame = StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER);
      Dafny.ISequence<byte> _14442_seqNumSeq;
      _14442_seqNumSeq = StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(sequenceNumber);
      _14441_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(_14441_unauthenticatedFrame, _14442_seqNumSeq);
      Dafny.ISequence<byte> _14443_iv;
      _14443_iv = MessageBody_Compile.__default.IVSeq(algorithmSuiteID, sequenceNumber);
      _14441_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(_14441_unauthenticatedFrame, _14443_iv);
      _14441_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(_14441_unauthenticatedFrame, StandardLibrary_mUInt_Compile.__default.UInt32ToSeq((uint)(plaintext).LongCount));
      Dafny.ISequence<byte> _14444_aad;
      Dafny.ISequence<byte> _out112;
      _out112 = MessageBody_Compile.__default.BodyAAD(messageID, @MessageBody_Compile.BodyAADContent.create_AADFinalFrame(), sequenceNumber, (ulong)(plaintext).LongCount);
      _14444_aad = _out112;
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _14445_encryptionOutputResult;
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _out113;
      _out113 = AESEncryption.__default.AESEncrypt(AlgorithmSuite.ID.EncryptionSuite(algorithmSuiteID), _14443_iv, key, plaintext, _14444_aad);
      _14445_encryptionOutputResult = _out113;
      if ((_14445_encryptionOutputResult).IsFailure()) {
        res = (_14445_encryptionOutputResult).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      AESEncryption.EncryptionOutput _14446_encryptionOutput;
      _14446_encryptionOutput = (_14445_encryptionOutputResult).Extract();
      _14441_unauthenticatedFrame = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_14441_unauthenticatedFrame, (_14446_encryptionOutput).dtor_cipherText), (_14446_encryptionOutput).dtor_authTag);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _rhs7 = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14441_unauthenticatedFrame);
      res = _rhs7;
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> DecryptFramedMessageBody(Streams_Compile.ByteReader rd, ushort algorithmSuiteID, Dafny.ISequence<byte> key, BigInteger frameLength, Dafny.ISequence<byte> messageID)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14447_plaintext;
      _14447_plaintext = Dafny.Sequence<byte>.FromElements();
      uint _14448_n;
      _14448_n = 1U;
      while (true) {
        MessageBody_Compile.FrameWithGhostSeq _14449_frameWithGhostSeq = MessageBody_Compile.FrameWithGhostSeq.Default();
        Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>> _14450_valueOrError0 = Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>>.Default(MessageBody_Compile.FrameWithGhostSeq.Default());
        Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>> _out114;
        _out114 = MessageBody_Compile.__default.DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, _14448_n);
        _14450_valueOrError0 = _out114;
        if ((_14450_valueOrError0).IsFailure()) {
          res = (_14450_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
          return res;
        }
        _14449_frameWithGhostSeq = (_14450_valueOrError0).Extract();
        MessageBody_Compile.Frame _14451_decryptedFrame;
        _14451_decryptedFrame = (_14449_frameWithGhostSeq).dtor_frame;
        _System.Tuple2<Dafny.ISequence<byte>, bool> _let_tmp_rhs1 = @_System.Tuple2<Dafny.ISequence<byte>, bool>.create((_14451_decryptedFrame).dtor_encContent, (_14451_decryptedFrame).is_FinalFrame);
        Dafny.ISequence<byte> _14452_decryptedFramePlaintext = ((_System.Tuple2<Dafny.ISequence<byte>, bool>)_let_tmp_rhs1)._0;
        bool _14453_final = ((_System.Tuple2<Dafny.ISequence<byte>, bool>)_let_tmp_rhs1)._1;
        _14447_plaintext = Dafny.Sequence<byte>.Concat(_14447_plaintext, _14452_decryptedFramePlaintext);
        if (_14453_final) {
          goto after_0;
        }
        _14448_n = (_14448_n) + (1U);
      }
    after_0: ;
      res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14447_plaintext);
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>> DecryptFrame(Streams_Compile.ByteReader rd, ushort algorithmSuiteID, Dafny.ISequence<byte> key, BigInteger frameLength, Dafny.ISequence<byte> messageID, uint expectedSequenceNumber)
    {
      Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>> res = Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>>.Default(MessageBody_Compile.FrameWithGhostSeq.Default());
      bool _14454_final;
      _14454_final = false;
      uint _14455_sequenceNumber = 0;
      Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _14456_valueOrError0 = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _out115;
      _out115 = (rd).ReadUInt32();
      _14456_valueOrError0 = _out115;
      if ((_14456_valueOrError0).IsFailure()) {
        res = (_14456_valueOrError0).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
        return res;
      }
      _14455_sequenceNumber = (_14456_valueOrError0).Extract();
      if ((_14455_sequenceNumber) == (MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER)) {
        _14454_final = true;
        Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _14457_valueOrError1 = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _out116;
        _out116 = (rd).ReadUInt32();
        _14457_valueOrError1 = _out116;
        if ((_14457_valueOrError1).IsFailure()) {
          res = (_14457_valueOrError1).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
          return res;
        }
        _14455_sequenceNumber = (_14457_valueOrError1).Extract();
      }
      if ((_14455_sequenceNumber) != (expectedSequenceNumber)) {
        res = @Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("unexpected frame sequence number"));
        return res;
      }
      Dafny.ISequence<byte> _14458_iv = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14459_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out117;
      _out117 = (rd).ReadBytes(AlgorithmSuite.ID.IVLength(algorithmSuiteID));
      _14459_valueOrError2 = _out117;
      if ((_14459_valueOrError2).IsFailure()) {
        res = (_14459_valueOrError2).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
        return res;
      }
      _14458_iv = (_14459_valueOrError2).Extract();
      uint _14460_len;
      _14460_len = (uint)(frameLength);
      if (_14454_final) {
        Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _14461_valueOrError3 = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
        Wrappers_Compile.Result<uint, Dafny.ISequence<char>> _out118;
        _out118 = (rd).ReadUInt32();
        _14461_valueOrError3 = _out118;
        if ((_14461_valueOrError3).IsFailure()) {
          res = (_14461_valueOrError3).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
          return res;
        }
        _14460_len = (_14461_valueOrError3).Extract();
        if ((_14460_len) > ((uint)(frameLength))) {
          res = @Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Final frame too long"));
          return res;
        }
      }
      Dafny.ISequence<byte> _14462_aad;
      Dafny.ISequence<byte> _out119;
      _out119 = MessageBody_Compile.__default.BodyAAD(messageID, ((_14454_final) ? (@MessageBody_Compile.BodyAADContent.create_AADFinalFrame()) : (@MessageBody_Compile.BodyAADContent.create_AADRegularFrame())), _14455_sequenceNumber, (ulong)(_14460_len));
      _14462_aad = _out119;
      Dafny.ISequence<byte> _14463_ciphertext = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14464_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out120;
      _out120 = (rd).ReadBytes(new BigInteger(_14460_len));
      _14464_valueOrError4 = _out120;
      if ((_14464_valueOrError4).IsFailure()) {
        res = (_14464_valueOrError4).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
        return res;
      }
      _14463_ciphertext = (_14464_valueOrError4).Extract();
      Dafny.ISequence<byte> _14465_authTag = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14466_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out121;
      _out121 = (rd).ReadBytes(AlgorithmSuite.ID.TagLength(algorithmSuiteID));
      _14466_valueOrError5 = _out121;
      if ((_14466_valueOrError5).IsFailure()) {
        res = (_14466_valueOrError5).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
        return res;
      }
      _14465_authTag = (_14466_valueOrError5).Extract();
      Dafny.ISequence<byte> _14467_plaintext = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14468_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out122;
      _out122 = MessageBody_Compile.__default.Decrypt(_14463_ciphertext, _14465_authTag, algorithmSuiteID, _14458_iv, key, _14462_aad);
      _14468_valueOrError6 = _out122;
      if ((_14468_valueOrError6).IsFailure()) {
        res = (_14468_valueOrError6).PropagateFailure<MessageBody_Compile.FrameWithGhostSeq>();
        return res;
      }
      _14467_plaintext = (_14468_valueOrError6).Extract();
      MessageBody_Compile.Frame _14469_frame;
      _14469_frame = ((_14454_final) ? (@MessageBody_Compile.Frame.create_FinalFrame(_14455_sequenceNumber, _14458_iv, _14467_plaintext, _14465_authTag)) : (@MessageBody_Compile.Frame.create_RegularFrame(_14455_sequenceNumber, _14458_iv, _14467_plaintext, _14465_authTag)));
      res = @Wrappers_Compile.Result<MessageBody_Compile.FrameWithGhostSeq, Dafny.ISequence<char>>.create_Success(@MessageBody_Compile.FrameWithGhostSeq.create(_14469_frame));
      return res;
      return res;
    }
    public static Dafny.ISequence<byte> BodyAAD(Dafny.ISequence<byte> messageID, MessageBody_Compile.BodyAADContent bc, uint sequenceNumber, ulong length)
    {
      Dafny.ISequence<byte> aad = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14470_contentAAD;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out123;
      _out123 = UTF8.__default.Encode(MessageBody_Compile.__default.BodyAADContentTypeString(bc));
      _14470_contentAAD = _out123;
      aad = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(messageID, (_14470_contentAAD).dtor_value), StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(sequenceNumber)), StandardLibrary_mUInt_Compile.__default.UInt64ToSeq(length));
      return aad;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Decrypt(Dafny.ISequence<byte> ciphertext, Dafny.ISequence<byte> authTag, ushort algorithmSuiteID, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> aad)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      EncryptionSuites.EncryptionSuite _14471_encAlg;
      _14471_encAlg = AlgorithmSuite.ID.EncryptionSuite(algorithmSuiteID);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out124;
      _out124 = AESEncryption.__default.AESDecrypt(_14471_encAlg, key, ciphertext, authTag, iv, aad);
      res = _out124;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> DecryptNonFramedMessageBody(Streams_Compile.ByteReader rd, ushort algorithmSuiteID, Dafny.ISequence<byte> key, Dafny.ISequence<byte> messageID)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _14472_iv = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14473_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out125;
      _out125 = (rd).ReadBytes(AlgorithmSuite.ID.IVLength(algorithmSuiteID));
      _14473_valueOrError0 = _out125;
      if ((_14473_valueOrError0).IsFailure()) {
        res = (_14473_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14472_iv = (_14473_valueOrError0).Extract();
      ulong _14474_contentLength = 0;
      Wrappers_Compile.Result<ulong, Dafny.ISequence<char>> _14475_valueOrError1 = Wrappers_Compile.Result<ulong, Dafny.ISequence<char>>.Default(0);
      Wrappers_Compile.Result<ulong, Dafny.ISequence<char>> _out126;
      _out126 = (rd).ReadUInt64();
      _14475_valueOrError1 = _out126;
      if ((_14475_valueOrError1).IsFailure()) {
        res = (_14475_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14474_contentLength = (_14475_valueOrError1).Extract();
      Dafny.ISequence<byte> _14476_ciphertext = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14477_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out127;
      _out127 = (rd).ReadBytes(new BigInteger(_14474_contentLength));
      _14477_valueOrError2 = _out127;
      if ((_14477_valueOrError2).IsFailure()) {
        res = (_14477_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14476_ciphertext = (_14477_valueOrError2).Extract();
      Dafny.ISequence<byte> _14478_authTag = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14479_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out128;
      _out128 = (rd).ReadBytes(AlgorithmSuite.ID.TagLength(algorithmSuiteID));
      _14479_valueOrError3 = _out128;
      if ((_14479_valueOrError3).IsFailure()) {
        res = (_14479_valueOrError3).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14478_authTag = (_14479_valueOrError3).Extract();
      Dafny.ISequence<byte> _14480_aad;
      Dafny.ISequence<byte> _out129;
      _out129 = MessageBody_Compile.__default.BodyAAD(messageID, @MessageBody_Compile.BodyAADContent.create_AADSingleBlock(), MessageBody_Compile.__default.NONFRAMED__SEQUENCE__NUMBER, _14474_contentLength);
      _14480_aad = _out129;
      Dafny.ISequence<byte> _14481_plaintext = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14482_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out130;
      _out130 = MessageBody_Compile.__default.Decrypt(_14476_ciphertext, _14478_authTag, algorithmSuiteID, _14472_iv, key, _14480_aad);
      _14482_valueOrError4 = _out130;
      if ((_14482_valueOrError4).IsFailure()) {
        res = (_14482_valueOrError4).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14481_plaintext = (_14482_valueOrError4).Extract();
      res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14481_plaintext);
      return res;
      return res;
    }
    public static uint START__SEQUENCE__NUMBER { get {
      return 1U;
    } }
    public static Dafny.ISequence<char> BODY__AAD__CONTENT__REGULAR__FRAME { get {
      return Dafny.Sequence<char>.FromString("AWSKMSEncryptionClient Frame");
    } }
    public static Dafny.ISequence<char> BODY__AAD__CONTENT__FINAL__FRAME { get {
      return Dafny.Sequence<char>.FromString("AWSKMSEncryptionClient Final Frame");
    } }
    public static Dafny.ISequence<char> BODY__AAD__CONTENT__SINGLE__BLOCK { get {
      return Dafny.Sequence<char>.FromString("AWSKMSEncryptionClient Single Block");
    } }
    public static uint ENDFRAME__SEQUENCE__NUMBER { get {
      return 4294967295U;
    } }
    public static uint NONFRAMED__SEQUENCE__NUMBER { get {
      return 1U;
    } }
  }
} // end of namespace MessageBody_Compile
namespace EncryptDecrypt {



















  public class EncryptRequest {
    public readonly Dafny.ISequence<byte> plaintext;
    public readonly Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm;
    public readonly Dafny.Aws.Crypto.IKeyring keyring;
    public readonly BigInteger plaintextLength;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext;
    public readonly Wrappers_Compile.Option<ushort> algorithmSuiteID;
    public readonly Wrappers_Compile.Option<uint> frameLength;
    public EncryptRequest(Dafny.ISequence<byte> plaintext, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm, Dafny.Aws.Crypto.IKeyring keyring, BigInteger plaintextLength, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<ushort> algorithmSuiteID, Wrappers_Compile.Option<uint> frameLength) {
      this.plaintext = plaintext;
      this.cmm = cmm;
      this.keyring = keyring;
      this.plaintextLength = plaintextLength;
      this.encryptionContext = encryptionContext;
      this.algorithmSuiteID = algorithmSuiteID;
      this.frameLength = frameLength;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptDecrypt.EncryptRequest;
      return oth != null && object.Equals(this.plaintext, oth.plaintext) && this.cmm == oth.cmm && this.keyring == oth.keyring && this.plaintextLength == oth.plaintextLength && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.algorithmSuiteID, oth.algorithmSuiteID) && object.Equals(this.frameLength, oth.frameLength);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cmm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyring));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frameLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptDecrypt_Compile.EncryptRequest.EncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cmm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyring);
      s += ", ";
      s += Dafny.Helpers.ToString(this.plaintextLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this.encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this.algorithmSuiteID);
      s += ", ";
      s += Dafny.Helpers.ToString(this.frameLength);
      s += ")";
      return s;
    }
    private static readonly EncryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, (Dafny.Aws.Crypto.ICryptographicMaterialsManager)null, (Dafny.Aws.Crypto.IKeyring)null, BigInteger.Zero, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, Wrappers_Compile.Option<ushort>.Default(), Wrappers_Compile.Option<uint>.Default());
    public static EncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptDecrypt.EncryptRequest> _TYPE = new Dafny.TypeDescriptor<EncryptDecrypt.EncryptRequest>(EncryptDecrypt.EncryptRequest.Default());
    public static Dafny.TypeDescriptor<EncryptDecrypt.EncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static EncryptRequest create(Dafny.ISequence<byte> plaintext, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm, Dafny.Aws.Crypto.IKeyring keyring, BigInteger plaintextLength, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Wrappers_Compile.Option<ushort> algorithmSuiteID, Wrappers_Compile.Option<uint> frameLength) {
      return new EncryptRequest(plaintext, cmm, keyring, plaintextLength, encryptionContext, algorithmSuiteID, frameLength);
    }
    public bool is_EncryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager dtor_cmm {
      get {
        return this.cmm;
      }
    }
    public Dafny.Aws.Crypto.IKeyring dtor_keyring {
      get {
        return this.keyring;
      }
    }
    public BigInteger dtor_plaintextLength {
      get {
        return this.plaintextLength;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Wrappers_Compile.Option<ushort> dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Wrappers_Compile.Option<uint> dtor_frameLength {
      get {
        return this.frameLength;
      }
    }
    public static EncryptDecrypt.EncryptRequest WithCMM(Dafny.ISequence<byte> plaintext, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm)
    {
      return @EncryptDecrypt.EncryptRequest.create(plaintext, cmm, (Dafny.Aws.Crypto.IKeyring)null, new BigInteger((plaintext).Count), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), @Wrappers_Compile.Option<ushort>.create_None(), @Wrappers_Compile.Option<uint>.create_None());
    }
    public static EncryptDecrypt.EncryptRequest WithKeyring(Dafny.ISequence<byte> plaintext, Dafny.Aws.Crypto.IKeyring keyring)
    {
      return @EncryptDecrypt.EncryptRequest.create(plaintext, (Dafny.Aws.Crypto.ICryptographicMaterialsManager)null, keyring, new BigInteger((plaintext).Count), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), @Wrappers_Compile.Option<ushort>.create_None(), @Wrappers_Compile.Option<uint>.create_None());
    }
    public EncryptDecrypt.EncryptRequest SetEncryptionContext(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext) {
      EncryptDecrypt.EncryptRequest _14483_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _14484_dt__update_hencryptionContext_h0 = encryptionContext;
      return @EncryptDecrypt.EncryptRequest.create((_14483_dt__update__tmp_h0).dtor_plaintext, (_14483_dt__update__tmp_h0).dtor_cmm, (_14483_dt__update__tmp_h0).dtor_keyring, (_14483_dt__update__tmp_h0).dtor_plaintextLength, _14484_dt__update_hencryptionContext_h0, (_14483_dt__update__tmp_h0).dtor_algorithmSuiteID, (_14483_dt__update__tmp_h0).dtor_frameLength);
    }
    public EncryptDecrypt.EncryptRequest SetAlgorithmSuiteID(ushort algorithmSuiteID) {
      EncryptDecrypt.EncryptRequest _14485_dt__update__tmp_h0 = this;
      Wrappers_Compile.Option<ushort> _14486_dt__update_halgorithmSuiteID_h0 = @Wrappers_Compile.Option<ushort>.create_Some(algorithmSuiteID);
      return @EncryptDecrypt.EncryptRequest.create((_14485_dt__update__tmp_h0).dtor_plaintext, (_14485_dt__update__tmp_h0).dtor_cmm, (_14485_dt__update__tmp_h0).dtor_keyring, (_14485_dt__update__tmp_h0).dtor_plaintextLength, (_14485_dt__update__tmp_h0).dtor_encryptionContext, _14486_dt__update_halgorithmSuiteID_h0, (_14485_dt__update__tmp_h0).dtor_frameLength);
    }
    public EncryptDecrypt.EncryptRequest SetFrameLength(uint frameLength) {
      EncryptDecrypt.EncryptRequest _14487_dt__update__tmp_h0 = this;
      Wrappers_Compile.Option<uint> _14488_dt__update_hframeLength_h0 = @Wrappers_Compile.Option<uint>.create_Some(frameLength);
      return @EncryptDecrypt.EncryptRequest.create((_14487_dt__update__tmp_h0).dtor_plaintext, (_14487_dt__update__tmp_h0).dtor_cmm, (_14487_dt__update__tmp_h0).dtor_keyring, (_14487_dt__update__tmp_h0).dtor_plaintextLength, (_14487_dt__update__tmp_h0).dtor_encryptionContext, (_14487_dt__update__tmp_h0).dtor_algorithmSuiteID, _14488_dt__update_hframeLength_h0);
    }
  }

  public class DecryptRequest {
    public readonly Dafny.ISequence<byte> message;
    public readonly Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm;
    public readonly Dafny.Aws.Crypto.IKeyring keyring;
    public DecryptRequest(Dafny.ISequence<byte> message, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm, Dafny.Aws.Crypto.IKeyring keyring) {
      this.message = message;
      this.cmm = cmm;
      this.keyring = keyring;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptDecrypt.DecryptRequest;
      return oth != null && object.Equals(this.message, oth.message) && this.cmm == oth.cmm && this.keyring == oth.keyring;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cmm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyring));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptDecrypt_Compile.DecryptRequest.DecryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this.message);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cmm);
      s += ", ";
      s += Dafny.Helpers.ToString(this.keyring);
      s += ")";
      return s;
    }
    private static readonly DecryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, (Dafny.Aws.Crypto.ICryptographicMaterialsManager)null, (Dafny.Aws.Crypto.IKeyring)null);
    public static DecryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptDecrypt.DecryptRequest> _TYPE = new Dafny.TypeDescriptor<EncryptDecrypt.DecryptRequest>(EncryptDecrypt.DecryptRequest.Default());
    public static Dafny.TypeDescriptor<EncryptDecrypt.DecryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptRequest create(Dafny.ISequence<byte> message, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm, Dafny.Aws.Crypto.IKeyring keyring) {
      return new DecryptRequest(message, cmm, keyring);
    }
    public bool is_DecryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this.message;
      }
    }
    public Dafny.Aws.Crypto.ICryptographicMaterialsManager dtor_cmm {
      get {
        return this.cmm;
      }
    }
    public Dafny.Aws.Crypto.IKeyring dtor_keyring {
      get {
        return this.keyring;
      }
    }
    public static EncryptDecrypt.DecryptRequest WithCMM(Dafny.ISequence<byte> message, Dafny.Aws.Crypto.ICryptographicMaterialsManager cmm)
    {
      return @EncryptDecrypt.DecryptRequest.create(message, cmm, (Dafny.Aws.Crypto.IKeyring)null);
    }
    public static EncryptDecrypt.DecryptRequest WithKeyring(Dafny.ISequence<byte> message, Dafny.Aws.Crypto.IKeyring keyring)
    {
      return @EncryptDecrypt.DecryptRequest.create(message, (Dafny.Aws.Crypto.ICryptographicMaterialsManager)null, keyring);
    }
  }

  public class DecryptResultWithVerificationInfo {
    public readonly Dafny.ISequence<byte> plaintext;
    public DecryptResultWithVerificationInfo(Dafny.ISequence<byte> plaintext) {
      this.plaintext = plaintext;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptDecrypt.DecryptResultWithVerificationInfo;
      return oth != null && object.Equals(this.plaintext, oth.plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptDecrypt_Compile.DecryptResultWithVerificationInfo.DecryptResultWithVerificationInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this.plaintext);
      s += ")";
      return s;
    }
    private static readonly DecryptResultWithVerificationInfo theDefault = create(Dafny.Sequence<byte>.Empty);
    public static DecryptResultWithVerificationInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<EncryptDecrypt.DecryptResultWithVerificationInfo> _TYPE = new Dafny.TypeDescriptor<EncryptDecrypt.DecryptResultWithVerificationInfo>(EncryptDecrypt.DecryptResultWithVerificationInfo.Default());
    public static Dafny.TypeDescriptor<EncryptDecrypt.DecryptResultWithVerificationInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static DecryptResultWithVerificationInfo create(Dafny.ISequence<byte> plaintext) {
      return new DecryptResultWithVerificationInfo(plaintext);
    }
    public bool is_DecryptResultWithVerificationInfo { get { return true; } }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Encrypt(EncryptDecrypt.EncryptRequest request)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      if ((((request).dtor_cmm) != (object) ((Dafny.Aws.Crypto.ICryptographicMaterialsManager)null)) && (((request).dtor_keyring) != (object) ((Dafny.Aws.Crypto.IKeyring)null))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("EncryptRequest.keyring OR EncryptRequest.cmm must be set (not both)."));
        return res;
      } else if ((((request).dtor_cmm) == (object) ((Dafny.Aws.Crypto.ICryptographicMaterialsManager)null)) && (((request).dtor_keyring) == (object) ((Dafny.Aws.Crypto.IKeyring)null))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("EncryptRequest.cmm and EncryptRequest.keyring cannot both be null."));
        return res;
      } else if ((((request).dtor_algorithmSuiteID).is_Some) && (!(AlgorithmSuite.__default.VALID__IDS).Contains((((request).dtor_algorithmSuiteID).dtor_value)))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Invalid algorithmSuiteID."));
        return res;
      } else if ((((request).dtor_frameLength).is_Some) && ((((request).dtor_frameLength).dtor_value) == (0U))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Request frameLength must be > 0"));
        return res;
      }
      Dafny.Aws.Crypto.ICryptographicMaterialsManager _14489_cmm = default(Dafny.Aws.Crypto.ICryptographicMaterialsManager);
      if (((request).dtor_keyring) == (object) ((Dafny.Aws.Crypto.IKeyring)null)) {
        _14489_cmm = (request).dtor_cmm;
      } else {
        DefaultCMMDef.DefaultCMM _nw11 = new DefaultCMMDef.DefaultCMM();
        _nw11.OfKeyring((request).dtor_keyring);
        _14489_cmm = _nw11;
      }
      uint _14490_frameLength;
      _14490_frameLength = ((((request).dtor_frameLength).is_Some) ? (((request).dtor_frameLength).dtor_value) : (EncryptDecrypt.__default.DEFAULT__FRAME__LENGTH));
      Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId> _14491_algorithmSuiteID;
      _14491_algorithmSuiteID = ((((request).dtor_algorithmSuiteID).is_Some) ? (@Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_Some(AlgorithmSuite.__default.InternalIDToPolymorphID((ushort)(((request).dtor_algorithmSuiteID).dtor_value)))) : (@Wrappers_Compile.Option<Dafny.Aws.Crypto.AlgorithmSuiteId>.create_None()));
      if (!(((request).dtor_plaintextLength) < (StandardLibrary_mUInt_Compile.__default.INT64__MAX__LIMIT))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(203,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Dafny.Aws.Crypto.GetEncryptionMaterialsInput _14492_encMatRequest;
      _14492_encMatRequest = @Dafny.Aws.Crypto.GetEncryptionMaterialsInput.create((request).dtor_encryptionContext, _14491_algorithmSuiteID, @Wrappers_Compile.Option<long>.create_Some((long)((request).dtor_plaintextLength)));
      Dafny.Aws.Crypto.GetEncryptionMaterialsOutput _14493_output = Dafny.Aws.Crypto.GetEncryptionMaterialsOutput.Default();
      Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>> _14494_valueOrError0 = Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.GetEncryptionMaterialsOutput.Default());
      Wrappers_Compile.Result<Dafny.Aws.Crypto.GetEncryptionMaterialsOutput, Dafny.ISequence<char>> _out131;
      _out131 = (_14489_cmm).GetEncryptionMaterials(_14492_encMatRequest);
      _14494_valueOrError0 = _out131;
      if ((_14494_valueOrError0).IsFailure()) {
        res = (_14494_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14493_output = (_14494_valueOrError0).Extract();
      Dafny.Aws.Crypto.EncryptionMaterials _14495_encMat;
      _14495_encMat = (_14493_output).dtor_encryptionMaterials;
      if (!(((_14495_encMat).dtor_plaintextDataKey).is_Some)) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(214,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(!(((_14491_algorithmSuiteID).is_None) || ((AlgorithmSuite.ID.SignatureType((ushort)(((request).dtor_algorithmSuiteID).dtor_value))).is_Some)) || (((_14495_encMat).dtor_encryptionContext).Contains((Materials.__default.EC__PUBLIC__KEY__FIELD))))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(215,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(DefaultCMMDef.__default.Serializable(_14495_encMat))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(217,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!(((System.Func<Wrappers_Compile.Option<ushort>, bool>)((_source22) => {
        if (_source22.is_None) {
          return (AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId)) == ((ushort)(888));
        } else {
          ushort _14496___mcc_h3 = ((Wrappers_Compile.Option_Some<ushort>)_source22).@value;
          return Dafny.Helpers.Let<ushort, bool>(_14496___mcc_h3, _pat_let7_0 => Dafny.Helpers.Let<ushort, bool>(_pat_let7_0, _14497_id => (AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId)) == ((ushort)(_14497_id))));
        }
      }))((request).dtor_algorithmSuiteID))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(218,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger((((_14495_encMat).dtor_plaintextDataKey).dtor_value).Count)) == (AlgorithmSuite.ID.KDFInputKeyLength(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId))))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(222,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if ((StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT) <= (new BigInteger(((_14495_encMat).dtor_encryptedDataKeys).Count))) {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Number of EDKs exceeds the allowed maximum."));
        return res;
      }
      Dafny.ISequence<byte> _14498_messageID = MessageHeader.MessageID.Default();
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14499_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out132;
      _out132 = Random_Compile.__default.GenerateBytes((int)(MessageHeader.__default.MESSAGE__ID__LEN));
      _14499_valueOrError1 = _out132;
      if ((_14499_valueOrError1).IsFailure()) {
        res = (_14499_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14498_messageID = (_14499_valueOrError1).Extract();
      Dafny.ISequence<byte> _14500_derivedDataKey;
      Dafny.ISequence<byte> _out133;
      _out133 = EncryptDecrypt.__default.DeriveKey(((_14495_encMat).dtor_plaintextDataKey).dtor_value, AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId), _14498_messageID);
      _14500_derivedDataKey = _out133;
      MessageHeader.HeaderBody _14501_headerBody;
      _14501_headerBody = @MessageHeader.HeaderBody.create(MessageHeader.__default.VERSION__1, MessageHeader.__default.TYPE__CUSTOMER__AED, AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId), _14498_messageID, (_14495_encMat).dtor_encryptionContext, @MessageHeader.EncryptedDataKeys.create((_14495_encMat).dtor_encryptedDataKeys), @MessageHeader.ContentType.create_Framed(), (byte)(AlgorithmSuite.ID.IVLength(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId))), _14490_frameLength);
      Streams_Compile.ByteWriter _14502_wr;
      Streams_Compile.ByteWriter _nw12 = new Streams_Compile.ByteWriter();
      _nw12.__ctor();
      _14502_wr = _nw12;
      BigInteger _14503___v2 = BigInteger.Zero;
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14504_valueOrError2 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out134;
      _out134 = Serialize_Compile.__default.SerializeHeaderBody(_14502_wr, _14501_headerBody);
      _14504_valueOrError2 = _out134;
      if ((_14504_valueOrError2).IsFailure()) {
        res = (_14504_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14503___v2 = (_14504_valueOrError2).Extract();
      Dafny.ISequence<byte> _14505_unauthenticatedHeader;
      _14505_unauthenticatedHeader = (_14502_wr).GetDataWritten();
      Dafny.ISequence<byte> _14506_iv;
      _14506_iv = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim10 = AlgorithmSuite.ID.IVLength(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId));
        var arr10 = new byte[Dafny.Helpers.ToIntChecked(dim10,"C# array size must not be larger than max 32-bit int")];
        for (int i10 = 0; i10 < dim10; i10++) {
          var _14507___v3 = (BigInteger) i10;
          arr10[(int)(_14507___v3)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr10);
      }))();
      AESEncryption.EncryptionOutput _14508_encryptionOutput = AESEncryption.EncryptionOutput.Default();
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _14509_valueOrError3 = Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>>.Default(AESEncryption.EncryptionOutput.Default());
      Wrappers_Compile.Result<AESEncryption.EncryptionOutput, Dafny.ISequence<char>> _out135;
      _out135 = AESEncryption.AES_GCM.AESEncryptExtern(AlgorithmSuite.ID.EncryptionSuite(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId)), _14506_iv, _14500_derivedDataKey, Dafny.Sequence<byte>.FromElements(), _14505_unauthenticatedHeader);
      _14509_valueOrError3 = _out135;
      if ((_14509_valueOrError3).IsFailure()) {
        res = (_14509_valueOrError3).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14508_encryptionOutput = (_14509_valueOrError3).Extract();
      MessageHeader.HeaderAuthentication _14510_headerAuthentication;
      _14510_headerAuthentication = @MessageHeader.HeaderAuthentication.create(_14506_iv, (_14508_encryptionOutput).dtor_authTag);
      BigInteger _14511___v5 = BigInteger.Zero;
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _14512_valueOrError4 = Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.Default(BigInteger.Zero);
      Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>> _out136;
      _out136 = Serialize_Compile.__default.SerializeHeaderAuthentication(_14502_wr, _14510_headerAuthentication);
      _14512_valueOrError4 = _out136;
      if ((_14512_valueOrError4).IsFailure()) {
        res = (_14512_valueOrError4).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14511___v5 = (_14512_valueOrError4).Extract();
      MessageBody_Compile.SeqWithGhostFrames _14513_seqWithGhostFrames = MessageBody_Compile.SeqWithGhostFrames.Default();
      Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>> _14514_valueOrError5 = Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>>.Default(MessageBody_Compile.SeqWithGhostFrames.Default());
      Wrappers_Compile.Result<MessageBody_Compile.SeqWithGhostFrames, Dafny.ISequence<char>> _out137;
      _out137 = MessageBody_Compile.__default.EncryptMessageBody((request).dtor_plaintext, new BigInteger(_14490_frameLength), _14498_messageID, _14500_derivedDataKey, AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId));
      _14514_valueOrError5 = _out137;
      if ((_14514_valueOrError5).IsFailure()) {
        res = (_14514_valueOrError5).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14513_seqWithGhostFrames = (_14514_valueOrError5).Extract();
      Dafny.ISequence<byte> _14515_body;
      _14515_body = (_14513_seqWithGhostFrames).dtor_sequence;
      Dafny.ISequence<byte> _14516_msg;
      _14516_msg = Dafny.Sequence<byte>.Concat((_14502_wr).GetDataWritten(), _14515_body);
      if ((AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId))).is_Some) {
        Signature.ECDSAParams _14517_ecdsaParams;
        _14517_ecdsaParams = (AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((_14495_encMat).dtor_algorithmSuiteId))).dtor_value;
        if (!(((_14495_encMat).dtor_signingKey).is_Some)) {
          throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(282,6): " + Dafny.Sequence<char>.FromString("expectation violation"));
        }
        Dafny.ISequence<byte> _14518_bytes = Dafny.Sequence<byte>.Empty;
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14519_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out138;
        _out138 = Signature.ECDSA.Sign(_14517_ecdsaParams, ((_14495_encMat).dtor_signingKey).dtor_value, _14516_msg);
        _14519_valueOrError6 = _out138;
        if ((_14519_valueOrError6).IsFailure()) {
          res = (_14519_valueOrError6).PropagateFailure<Dafny.ISequence<byte>>();
          return res;
        }
        _14518_bytes = (_14519_valueOrError6).Extract();
        if ((new BigInteger((_14518_bytes).Count)) != (new BigInteger((_14517_ecdsaParams).SignatureLength()))) {
          res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Malformed response from Sign()."));
          return res;
        }
        Dafny.ISequence<byte> _14520_signature;
        _14520_signature = Dafny.Sequence<byte>.Concat(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)(_14518_bytes).Count), _14518_bytes);
        _14516_msg = Dafny.Sequence<byte>.Concat(_14516_msg, _14520_signature);
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14516_msg);
        return res;
      } else {
        res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_14516_msg);
        return res;
      }
      return res;
    }
    public static Dafny.ISequence<byte> DeriveKey(Dafny.ISequence<byte> plaintextDataKey, ushort algorithmSuiteID, Dafny.ISequence<byte> messageID)
    {
      Dafny.ISequence<byte> derivedDataKey = Dafny.Sequence<byte>.Empty;
      KeyDerivationAlgorithms.KeyDerivationAlgorithm _14521_algorithm;
      _14521_algorithm = (Dafny.Map<ushort, AlgorithmSuite.AlgSuite>.Select(AlgorithmSuite.__default.Suite,algorithmSuiteID)).dtor_hkdf;
      if (object.Equals(_14521_algorithm, @KeyDerivationAlgorithms.KeyDerivationAlgorithm.create_IDENTITY())) {
        derivedDataKey = plaintextDataKey;
        return derivedDataKey;
      }
      Dafny.ISequence<byte> _14522_infoSeq;
      _14522_infoSeq = Dafny.Sequence<byte>.Concat(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)(algorithmSuiteID)), messageID);
      BigInteger _14523_len;
      _14523_len = AlgorithmSuite.ID.KeyLength(algorithmSuiteID);
      Dafny.ISequence<byte> _14524_derivedKey;
      Dafny.ISequence<byte> _out139;
      _out139 = HKDF_Compile.__default.Hkdf(_14521_algorithm, @Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), plaintextDataKey, _14522_infoSeq, _14523_len);
      _14524_derivedKey = _out139;
      derivedDataKey = _14524_derivedKey;
      return derivedDataKey;
      return derivedDataKey;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> Decrypt(EncryptDecrypt.DecryptRequest request)
    {
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      EncryptDecrypt.DecryptResultWithVerificationInfo _14525_decryptWithVerificationInfo = EncryptDecrypt.DecryptResultWithVerificationInfo.Default();
      Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>> _14526_valueOrError0 = Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.Default(EncryptDecrypt.DecryptResultWithVerificationInfo.Default());
      Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>> _out140;
      _out140 = EncryptDecrypt.__default.DecryptWithVerificationInfo(request);
      _14526_valueOrError0 = _out140;
      if ((_14526_valueOrError0).IsFailure()) {
        res = (_14526_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _14525_decryptWithVerificationInfo = (_14526_valueOrError0).Extract();
      res = @Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success((_14525_decryptWithVerificationInfo).dtor_plaintext);
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>> DecryptWithVerificationInfo(EncryptDecrypt.DecryptRequest request)
    {
      Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>> res = Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.Default(EncryptDecrypt.DecryptResultWithVerificationInfo.Default());
      if ((((request).dtor_cmm) != (object) ((Dafny.Aws.Crypto.ICryptographicMaterialsManager)null)) && (((request).dtor_keyring) != (object) ((Dafny.Aws.Crypto.IKeyring)null))) {
        res = @Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("DecryptRequest.keyring OR DecryptRequest.cmm must be set (not both)."));
        return res;
      } else if ((((request).dtor_cmm) == (object) ((Dafny.Aws.Crypto.ICryptographicMaterialsManager)null)) && (((request).dtor_keyring) == (object) ((Dafny.Aws.Crypto.IKeyring)null))) {
        res = @Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("DecryptRequest.cmm and DecryptRequest.keyring cannot both be null."));
        return res;
      }
      Dafny.Aws.Crypto.ICryptographicMaterialsManager _14527_cmm = default(Dafny.Aws.Crypto.ICryptographicMaterialsManager);
      if (((request).dtor_keyring) == (object) ((Dafny.Aws.Crypto.IKeyring)null)) {
        _14527_cmm = (request).dtor_cmm;
      } else {
        DefaultCMMDef.DefaultCMM _nw13 = new DefaultCMMDef.DefaultCMM();
        _nw13.OfKeyring((request).dtor_keyring);
        _14527_cmm = _nw13;
      }
      Streams_Compile.ByteReader _14528_rd;
      Streams_Compile.ByteReader _nw14 = new Streams_Compile.ByteReader();
      _nw14.__ctor((request).dtor_message);
      _14528_rd = _nw14;
      Deserialize_Compile.DeserializeHeaderResult _14529_deserializeHeaderResult = Deserialize_Compile.DeserializeHeaderResult.Default();
      Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>> _14530_valueOrError0 = Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>>.Default(Deserialize_Compile.DeserializeHeaderResult.Default());
      Wrappers_Compile.Result<Deserialize_Compile.DeserializeHeaderResult, Dafny.ISequence<char>> _out141;
      _out141 = Deserialize_Compile.__default.DeserializeHeader(_14528_rd);
      _14530_valueOrError0 = _out141;
      if ((_14530_valueOrError0).IsFailure()) {
        res = (_14530_valueOrError0).PropagateFailure<EncryptDecrypt.DecryptResultWithVerificationInfo>();
        return res;
      }
      _14529_deserializeHeaderResult = (_14530_valueOrError0).Extract();
      MessageHeader.Header _14531_header;
      _14531_header = (_14529_deserializeHeaderResult).dtor_header;
      Dafny.Aws.Crypto.DecryptMaterialsInput _14532_decMatRequest;
      _14532_decMatRequest = @Dafny.Aws.Crypto.DecryptMaterialsInput.create(AlgorithmSuite.__default.InternalIDToPolymorphID(((_14531_header).dtor_body).dtor_algorithmSuiteID), (((_14531_header).dtor_body).dtor_encryptedDataKeys).dtor_entries, ((_14531_header).dtor_body).dtor_aad);
      Dafny.Aws.Crypto.DecryptMaterialsOutput _14533_output = Dafny.Aws.Crypto.DecryptMaterialsOutput.Default();
      Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>> _14534_valueOrError1 = Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Crypto.DecryptMaterialsOutput.Default());
      Wrappers_Compile.Result<Dafny.Aws.Crypto.DecryptMaterialsOutput, Dafny.ISequence<char>> _out142;
      _out142 = (_14527_cmm).DecryptMaterials(_14532_decMatRequest);
      _14534_valueOrError1 = _out142;
      if ((_14534_valueOrError1).IsFailure()) {
        res = (_14534_valueOrError1).PropagateFailure<EncryptDecrypt.DecryptResultWithVerificationInfo>();
        return res;
      }
      _14533_output = (_14534_valueOrError1).Extract();
      Dafny.Aws.Crypto.DecryptionMaterials _14535_decMat;
      _14535_decMat = (_14533_output).dtor_decryptionMaterials;
      if (!(((_14535_decMat).dtor_plaintextDataKey).is_Some)) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(404,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      if (!((new BigInteger((((_14535_decMat).dtor_plaintextDataKey).dtor_value).Count)) == (AlgorithmSuite.ID.KDFInputKeyLength(AlgorithmSuite.__default.PolymorphIDToInternalID((_14535_decMat).dtor_algorithmSuiteId))))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(405,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Dafny.ISequence<byte> _14536_decryptionKey;
      Dafny.ISequence<byte> _out143;
      _out143 = EncryptDecrypt.__default.DeriveKey(((_14535_decMat).dtor_plaintextDataKey).dtor_value, AlgorithmSuite.__default.PolymorphIDToInternalID((_14535_decMat).dtor_algorithmSuiteId), ((_14531_header).dtor_body).dtor_messageID);
      _14536_decryptionKey = _out143;
      Dafny.ISequence<byte> _14537_plaintext = Dafny.Sequence<byte>.Empty;
      MessageHeader.ContentType _source23 = ((_14531_header).dtor_body).dtor_contentType;
      if (_source23.is_NonFramed) {
        {
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14538_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out144;
          _out144 = MessageBody_Compile.__default.DecryptNonFramedMessageBody(_14528_rd, AlgorithmSuite.__default.PolymorphIDToInternalID((_14535_decMat).dtor_algorithmSuiteId), _14536_decryptionKey, ((_14531_header).dtor_body).dtor_messageID);
          _14538_valueOrError2 = _out144;
          if ((_14538_valueOrError2).IsFailure()) {
            res = (_14538_valueOrError2).PropagateFailure<EncryptDecrypt.DecryptResultWithVerificationInfo>();
            return res;
          }
          _14537_plaintext = (_14538_valueOrError2).Extract();
        }
      } else {
        {
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14539_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
          Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out145;
          _out145 = MessageBody_Compile.__default.DecryptFramedMessageBody(_14528_rd, AlgorithmSuite.__default.PolymorphIDToInternalID((_14535_decMat).dtor_algorithmSuiteId), _14536_decryptionKey, new BigInteger(((_14531_header).dtor_body).dtor_frameLength), ((_14531_header).dtor_body).dtor_messageID);
          _14539_valueOrError3 = _out145;
          if ((_14539_valueOrError3).IsFailure()) {
            res = (_14539_valueOrError3).PropagateFailure<EncryptDecrypt.DecryptResultWithVerificationInfo>();
            return res;
          }
          _14537_plaintext = (_14539_valueOrError3).Extract();
        }
      }
      if ((AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((_14535_decMat).dtor_algorithmSuiteId))).is_Some) {
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _14540_verifyResult;
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _out146;
        _out146 = EncryptDecrypt.__default.VerifySignature(_14528_rd, _14535_decMat);
        _14540_verifyResult = _out146;
        if ((_14540_verifyResult).is_Failure) {
          res = @Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.create_Failure((_14540_verifyResult).dtor_error);
          return res;
        }
      }
      bool _14541_isDone;
      bool _out147;
      _out147 = (_14528_rd).IsDoneReading();
      _14541_isDone = _out147;
      if (!(_14541_isDone)) {
        res = @Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("message contains additional bytes at end"));
        return res;
      }
      EncryptDecrypt.DecryptResultWithVerificationInfo _14542_decryptResultWithVerificationInfo;
      _14542_decryptResultWithVerificationInfo = @EncryptDecrypt.DecryptResultWithVerificationInfo.create(_14537_plaintext);
      res = @Wrappers_Compile.Result<EncryptDecrypt.DecryptResultWithVerificationInfo, Dafny.ISequence<char>>.create_Success(_14542_decryptResultWithVerificationInfo);
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> VerifySignature(Streams_Compile.ByteReader rd, Dafny.Aws.Crypto.DecryptionMaterials decMat)
    {
      Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> res = Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.Default(_System.Tuple0.Default());
      if (!((AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((decMat).dtor_algorithmSuiteId))).is_Some)) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(522,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Signature.ECDSAParams _14543_ecdsaParams;
      _14543_ecdsaParams = (AlgorithmSuite.ID.SignatureType(AlgorithmSuite.__default.PolymorphIDToInternalID((decMat).dtor_algorithmSuiteId))).dtor_value;
      BigInteger _14544_usedCapacity;
      BigInteger _out148;
      _out148 = (rd).GetSizeRead();
      _14544_usedCapacity = _out148;
      Dafny.ISequence<byte> _14545_msg;
      _14545_msg = (((rd).reader).data).Take(_14544_usedCapacity);
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _14546_signatureLengthResult;
      Wrappers_Compile.Result<ushort, Dafny.ISequence<char>> _out149;
      _out149 = (rd).ReadUInt16();
      _14546_signatureLengthResult = _out149;
      if ((_14546_signatureLengthResult).is_Failure) {
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _rhs8 = @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Failure((_14546_signatureLengthResult).dtor_error);
        res = _rhs8;
        return res;
      }
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14547_sigResult;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out150;
      _out150 = (rd).ReadBytes(new BigInteger((_14546_signatureLengthResult).dtor_value));
      _14547_sigResult = _out150;
      if ((_14547_sigResult).is_Failure) {
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _rhs9 = @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Failure((_14547_sigResult).dtor_error);
        res = _rhs9;
        return res;
      }
      if (!(((decMat).dtor_verificationKey).is_Some)) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/EncryptDecrypt.dfy(538,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Wrappers_Compile.Result<bool, Dafny.ISequence<char>> _14548_signatureVerifiedResult;
      Wrappers_Compile.Result<bool, Dafny.ISequence<char>> _out151;
      _out151 = Signature.ECDSA.Verify(_14543_ecdsaParams, ((decMat).dtor_verificationKey).dtor_value, _14545_msg, (_14547_sigResult).dtor_value);
      _14548_signatureVerifiedResult = _out151;
      if ((_14548_signatureVerifiedResult).is_Failure) {
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _rhs10 = @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Failure((_14548_signatureVerifiedResult).dtor_error);
        res = _rhs10;
        return res;
      }
      if (!((_14548_signatureVerifiedResult).dtor_value)) {
        Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _rhs11 = @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("signature not verified"));
        res = _rhs11;
        return res;
      }
      Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> _rhs12 = @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Success(@_System.Tuple0.create());
      res = _rhs12;
      return res;
      return res;
    }
    public static uint DEFAULT__FRAME__LENGTH { get {
      return 4096U;
    } }
  }
} // end of namespace EncryptDecrypt
namespace Dafny.Aws.Esdk.AwsEncryptionSdkClient {








  public partial class AwsEncryptionSdkClient : Dafny.Aws.Esdk.IAwsEncryptionSdkClient {
    public AwsEncryptionSdkClient() {
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile.Result<Dafny.Aws.Esdk.EncryptOutput, Dafny.ISequence<char>> Encrypt(Dafny.Aws.Esdk.EncryptInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Esdk.EncryptOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Esdk.EncryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Esdk.EncryptOutput.Default());
      EncryptDecrypt.EncryptRequest _14549_encryptRequest;
      _14549_encryptRequest = (EncryptDecrypt.EncryptRequest.WithCMM((input).dtor_plaintext, (input).dtor_materialsManager)).SetEncryptionContext((input).dtor_encryptionContext);
      Dafny.ISequence<byte> _14550_e = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14551_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out152;
      _out152 = EncryptDecrypt.__default.Encrypt(_14549_encryptRequest);
      _14551_valueOrError0 = _out152;
      if (!(!((_14551_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/AwsEncryptionSdk.dfy(30,18): " + _14551_valueOrError0);
      }
      _14550_e = (_14551_valueOrError0).Extract();
      res = @Wrappers_Compile.Result<Dafny.Aws.Esdk.EncryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Esdk.EncryptOutput.create(_14550_e));
      return res;
      return res;
    }
    public Wrappers_Compile.Result<Dafny.Aws.Esdk.DecryptOutput, Dafny.ISequence<char>> Decrypt(Dafny.Aws.Esdk.DecryptInput input)
    {
      Wrappers_Compile.Result<Dafny.Aws.Esdk.DecryptOutput, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.Aws.Esdk.DecryptOutput, Dafny.ISequence<char>>.Default(Dafny.Aws.Esdk.DecryptOutput.Default());
      EncryptDecrypt.DecryptRequest _14552_decryptRequest;
      _14552_decryptRequest = EncryptDecrypt.DecryptRequest.WithCMM((input).dtor_ciphertext, (input).dtor_materialsManager);
      Dafny.ISequence<byte> _14553_d = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14554_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out153;
      _out153 = EncryptDecrypt.__default.Decrypt(_14552_decryptRequest);
      _14554_valueOrError0 = _out153;
      if (!(!((_14554_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/farleyb/workspace/esdk/dafny/aws-encryption-sdk-dafny/src/SDK/AwsEncryptionSdk.dfy(37,18): " + _14554_valueOrError0);
      }
      _14553_d = (_14554_valueOrError0).Extract();
      res = @Wrappers_Compile.Result<Dafny.Aws.Esdk.DecryptOutput, Dafny.ISequence<char>>.create_Success(@Dafny.Aws.Esdk.DecryptOutput.create(_14553_d));
      return res;
      return res;
    }
  }

} // end of namespace Dafny.Aws.Esdk.AwsEncryptionSdkClient
namespace AwsKmsMrkAreUnique_Compile {





  public partial class __default {
    public static Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>> AwsKmsMrkAreUnique(Dafny.ISequence<AwsKmsArnParsing_Compile.AwsKmsIdentifier> identifiers) {
      Dafny.ISequence<AwsKmsArnParsing_Compile.AwsKmsIdentifier> _14555_mrks = Seq_Compile.__default.Filter<AwsKmsArnParsing_Compile.AwsKmsIdentifier>(AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsIdentifier, identifiers);
      if ((new BigInteger((_14555_mrks).Count)).Sign == 0) {
        return @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Success(@_System.Tuple0.create());
      } else {
        Dafny.ISequence<Dafny.ISequence<char>> _14556_mrkKeyIds = Seq_Compile.__default.Map<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>>(AwsKmsMrkAreUnique_Compile.__default.GetKeyId, _14555_mrks);
        Dafny.ISet<Dafny.ISequence<char>> _14557_setMrks = Seq_Compile.__default.ToSet<Dafny.ISequence<char>>(_14556_mrkKeyIds);
        if ((new BigInteger((_14556_mrkKeyIds).Count)) == (new BigInteger((_14557_setMrks).Count))) {
          return @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Success(@_System.Tuple0.create());
        } else {
          Dafny.ISet<Dafny.ISequence<char>> _14558_duplicateMrkIds = Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISet<Dafny.ISequence<char>>>>((_14559_mrkKeyIds) => ((System.Func<Dafny.ISet<Dafny.ISequence<char>>>)(() => {
            var _coll1 = new System.Collections.Generic.List<Dafny.ISequence<char>>();
            foreach (Dafny.ISequence<char> _compr_1 in (_14559_mrkKeyIds).Elements) {
              Dafny.ISequence<char> _14560_x = (Dafny.ISequence<char>)_compr_1;
              if (((_14559_mrkKeyIds).Contains((_14560_x))) && (((Dafny.MultiSet<Dafny.ISequence<char>>.FromSeq(_14559_mrkKeyIds)).Select(_14560_x)) >= (BigInteger.One))) {
                _coll1.Add(_14560_x);
              }
            }
            return Dafny.Set<Dafny.ISequence<char>>.FromCollection(_coll1);
          }))())(_14556_mrkKeyIds);
          Func<AwsKmsArnParsing_Compile.AwsKmsIdentifier, bool> _14561_isDuplicate = Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<char>>, Func<AwsKmsArnParsing_Compile.AwsKmsIdentifier, bool>>>((_14562_duplicateMrkIds) => ((System.Func<AwsKmsArnParsing_Compile.AwsKmsIdentifier, bool>)((_14563_identifier) => {
            return (_14562_duplicateMrkIds).Contains((AwsKmsMrkAreUnique_Compile.__default.GetKeyId(_14563_identifier)));
          })))(_14558_duplicateMrkIds);
          Func<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>> _14564_identifierToString = ((System.Func<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>>)((_14565_i) => {
            return (_14565_i)._ToString();
          }));
          Dafny.ISequence<AwsKmsArnParsing_Compile.AwsKmsIdentifier> _14566_duplicateIdentifiers = Seq_Compile.__default.Filter<AwsKmsArnParsing_Compile.AwsKmsIdentifier>(_14561_isDuplicate, identifiers);
          Dafny.ISequence<Dafny.ISequence<char>> _14567_duplicates = Seq_Compile.__default.Map<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>>(_14564_identifierToString, _14566_duplicateIdentifiers);
          Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14568_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((new BigInteger((_14567_duplicates).Count)).Sign == 1, Dafny.Sequence<char>.FromString("Impossible"));
          if ((_14568_valueOrError0).IsFailure()) {
            return (_14568_valueOrError0).PropagateFailure<_System.Tuple0>();
          } else {
            return @Wrappers_Compile.Result<_System.Tuple0, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Related multi-Region keys: "), StandardLibrary_Compile.__default.Join<char>(_14567_duplicates, Dafny.Sequence<char>.FromString(","))), Dafny.Sequence<char>.FromString("are not allowed.")));
          }
        }
      }
    }
    public static Dafny.ISequence<char> GetKeyId(AwsKmsArnParsing_Compile.AwsKmsIdentifier identifier) {
      AwsKmsArnParsing_Compile.AwsKmsIdentifier _source24 = identifier;
      if (_source24.is_AwsKmsArnIdentifier) {
        AwsKmsArnParsing_Compile.AwsArn _14569___mcc_h0 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source24).a;
        AwsKmsArnParsing_Compile.AwsArn _14570_a = _14569___mcc_h0;
        return ((_14570_a).dtor_resource).dtor_value;
      } else {
        AwsKmsArnParsing_Compile.AwsResource _14571___mcc_h1 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source24).r;
        AwsKmsArnParsing_Compile.AwsResource _14572_i = _14571___mcc_h1;
        return (_14572_i).dtor_value;
      }
    }
  }
} // end of namespace AwsKmsMrkAreUnique_Compile
namespace Actions_Compile {


  public interface Action<A, R> {
    R Invoke(A a);
  }
  public class _Companion_Action<A, R> {
  }

  public interface ActionWithResult<A, R, E> : Actions_Compile.Action<A, Wrappers_Compile.Result<R, E>> {
  }
  public class _Companion_ActionWithResult<A, R, E> {
  }

  public partial class __default {
    public static Dafny.ISequence<__R> Map<__A, __R>(Actions_Compile.Action<__A, __R> action, Dafny.ISequence<__A> s)
    {
      Dafny.ISequence<__R> res = Dafny.Sequence<__R>.Empty;
      Dafny.ISequence<__R> _14573_rs;
      _14573_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi0 = new BigInteger((s).Count);
      for (BigInteger _14574_i = BigInteger.Zero; _14574_i < _hi0; _14574_i++) {
        __R _14575_r;
        __R _out154;
        _out154 = (action).Invoke((s).Select(_14574_i));
        _14575_r = _out154;
        _14573_rs = Dafny.Sequence<__R>.Concat(_14573_rs, Dafny.Sequence<__R>.FromElements(_14575_r));
      }
      res = _14573_rs;
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<__R>, __E> MapWithResult<__A, __R, __E>(Dafny.TypeDescriptor<__R> _td___R, Actions_Compile.ActionWithResult<__A, __R, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile.Result<Dafny.ISequence<__R>, __E> res = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.Default(Dafny.Sequence<__R>.Empty);
      Dafny.ISequence<__R> _14576_rs;
      _14576_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi1 = new BigInteger((s).Count);
      for (BigInteger _14577_i = BigInteger.Zero; _14577_i < _hi1; _14577_i++) {
        __R _14578_r = _td___R.Default();
        Wrappers_Compile.Result<__R, __E> _14579_valueOrError0 = Wrappers_Compile.Result<__R, __E>.Default(_td___R.Default());
        Wrappers_Compile.Result<__R, __E> _out155;
        _out155 = (action).Invoke((s).Select(_14577_i));
        _14579_valueOrError0 = _out155;
        if ((_14579_valueOrError0).IsFailure()) {
          res = (_14579_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
          return res;
        }
        _14578_r = (_14579_valueOrError0).Extract();
        _14576_rs = Dafny.Sequence<__R>.Concat(_14576_rs, Dafny.Sequence<__R>.FromElements(_14578_r));
      }
      res = @Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(_14576_rs);
      return res;
      return res;
    }
    public static Dafny.ISequence<__A> Filter<__A>(Actions_Compile.Action<__A, bool> action, Dafny.ISequence<__A> s)
    {
      Dafny.ISequence<__A> res = Dafny.Sequence<__A>.Empty;
      Dafny.ISequence<__A> _14580_rs;
      _14580_rs = Dafny.Sequence<__A>.FromElements();
      BigInteger _hi2 = new BigInteger((s).Count);
      for (BigInteger _14581_i = BigInteger.Zero; _14581_i < _hi2; _14581_i++) {
        bool _14582_r;
        bool _out156;
        _out156 = (action).Invoke((s).Select(_14581_i));
        _14582_r = _out156;
        if (_14582_r) {
          _14580_rs = Dafny.Sequence<__A>.Concat(_14580_rs, Dafny.Sequence<__A>.FromElements((s).Select(_14581_i)));
        }
      }
      res = _14580_rs;
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<Dafny.ISequence<__A>, __E> FilterWithResult<__A, __E>(Actions_Compile.ActionWithResult<__A, bool, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile.Result<Dafny.ISequence<__A>, __E> res = Wrappers_Compile.Result<Dafny.ISequence<__A>, __E>.Default(Dafny.Sequence<__A>.Empty);
      Dafny.ISequence<__A> _14583_rs;
      _14583_rs = Dafny.Sequence<__A>.FromElements();
      BigInteger _hi3 = new BigInteger((s).Count);
      for (BigInteger _14584_i = BigInteger.Zero; _14584_i < _hi3; _14584_i++) {
        bool _14585_r = false;
        Wrappers_Compile.Result<bool, __E> _14586_valueOrError0 = Wrappers_Compile.Result<bool, __E>.Default(false);
        Wrappers_Compile.Result<bool, __E> _out157;
        _out157 = (action).Invoke((s).Select(_14584_i));
        _14586_valueOrError0 = _out157;
        if ((_14586_valueOrError0).IsFailure()) {
          res = (_14586_valueOrError0).PropagateFailure<Dafny.ISequence<__A>>();
          return res;
        }
        _14585_r = (_14586_valueOrError0).Extract();
        if (_14585_r) {
          _14583_rs = Dafny.Sequence<__A>.Concat(_14583_rs, Dafny.Sequence<__A>.FromElements((s).Select(_14584_i)));
        }
      }
      res = @Wrappers_Compile.Result<Dafny.ISequence<__A>, __E>.create_Success(_14583_rs);
      return res;
      return res;
    }
    public static Wrappers_Compile.Result<__B, Dafny.ISequence<__E>> ReduceToSuccess<__A, __B, __E>(Actions_Compile.ActionWithResult<__A, __B, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile.Result<__B, Dafny.ISequence<__E>> res = default(Wrappers_Compile.Result<__B, Dafny.ISequence<__E>>);
      Dafny.ISequence<__E> _14587_errors;
      _14587_errors = Dafny.Sequence<__E>.FromElements();
      BigInteger _hi4 = new BigInteger((s).Count);
      for (BigInteger _14588_i = BigInteger.Zero; _14588_i < _hi4; _14588_i++) {
        Wrappers_Compile.Result<__B, __E> _14589_attempt;
        Wrappers_Compile.Result<__B, __E> _out158;
        _out158 = (action).Invoke((s).Select(_14588_i));
        _14589_attempt = _out158;
        if ((_14589_attempt).is_Success) {
          res = @Wrappers_Compile.Result<__B, Dafny.ISequence<__E>>.create_Success((_14589_attempt).dtor_value);
          return res;
        } else {
          _14587_errors = Dafny.Sequence<__E>.Concat(_14587_errors, Dafny.Sequence<__E>.FromElements((_14589_attempt).dtor_error));
        }
      }
      res = @Wrappers_Compile.Result<__B, Dafny.ISequence<__E>>.create_Failure(_14587_errors);
      return res;
      return res;
    }
  }
} // end of namespace Actions_Compile
namespace Constants_Compile {


  public partial class __default {
    public static Dafny.ISequence<byte> PROVIDER__ID { get {
      Dafny.ISequence<byte> _14590_s = Dafny.Sequence<byte>.FromElements(97, 119, 115, 45, 107, 109, 115);
      return _14590_s;
    } }
  }
} // end of namespace Constants_Compile
namespace AwsKmsMrkMatchForDecrypt_Compile {





  public partial class __default {
    public static bool AwsKmsMrkMatchForDecrypt(AwsKmsArnParsing_Compile.AwsKmsIdentifier configuredAwsKmsIdentifier, AwsKmsArnParsing_Compile.AwsKmsIdentifier messageAwsKmsIdentifer)
    {
      if (object.Equals(configuredAwsKmsIdentifier, messageAwsKmsIdentifer)) {
        return true;
      } else {
        _System.Tuple2<AwsKmsArnParsing_Compile.AwsKmsIdentifier, AwsKmsArnParsing_Compile.AwsKmsIdentifier> _source25 = @_System.Tuple2<AwsKmsArnParsing_Compile.AwsKmsIdentifier, AwsKmsArnParsing_Compile.AwsKmsIdentifier>.create(messageAwsKmsIdentifer, configuredAwsKmsIdentifier);
        {
          AwsKmsArnParsing_Compile.AwsKmsIdentifier _14591___mcc_h0 = ((_System.Tuple2<AwsKmsArnParsing_Compile.AwsKmsIdentifier, AwsKmsArnParsing_Compile.AwsKmsIdentifier>)_source25)._0;
          AwsKmsArnParsing_Compile.AwsKmsIdentifier _14592___mcc_h1 = ((_System.Tuple2<AwsKmsArnParsing_Compile.AwsKmsIdentifier, AwsKmsArnParsing_Compile.AwsKmsIdentifier>)_source25)._1;
          AwsKmsArnParsing_Compile.AwsKmsIdentifier _source26 = _14591___mcc_h0;
          if (_source26.is_AwsKmsArnIdentifier) {
            AwsKmsArnParsing_Compile.AwsArn _14593___mcc_h2 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source26).a;
            AwsKmsArnParsing_Compile.AwsKmsIdentifier _source27 = _14592___mcc_h1;
            if (_source27.is_AwsKmsArnIdentifier) {
              AwsKmsArnParsing_Compile.AwsArn _14594___mcc_h4 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsArnIdentifier)_source27).a;
              AwsKmsArnParsing_Compile.AwsArn _14595_messageAwsKmsArn = _14594___mcc_h4;
              AwsKmsArnParsing_Compile.AwsArn _14596_configuredAwsKmsArn = _14593___mcc_h2;
              if ((!(AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsArn(_14596_configuredAwsKmsArn))) || (!(AwsKmsArnParsing_Compile.__default.IsMultiRegionAwsKmsArn(_14595_messageAwsKmsArn)))) {
                return false;
              } else {
                return (((((_14595_messageAwsKmsArn).dtor_partition).Equals(((_14596_configuredAwsKmsArn).dtor_partition))) && (((_14595_messageAwsKmsArn).dtor_service).Equals(((_14596_configuredAwsKmsArn).dtor_service)))) && (((_14595_messageAwsKmsArn).dtor_account).Equals(((_14596_configuredAwsKmsArn).dtor_account)))) && (object.Equals((_14595_messageAwsKmsArn).dtor_resource, (_14596_configuredAwsKmsArn).dtor_resource));
              }
            } else {
              AwsKmsArnParsing_Compile.AwsResource _14597___mcc_h6 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source27).r;
              return false;
            }
          } else {
            AwsKmsArnParsing_Compile.AwsResource _14598___mcc_h8 = ((AwsKmsArnParsing_Compile.AwsKmsIdentifier_AwsKmsRawResourceIdentifier)_source26).r;
            return false;
          }
        }
      }
    }
  }
} // end of namespace AwsKmsMrkMatchForDecrypt_Compile
namespace KeyringDefs {





  public interface Keyring {
    Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>> OnEncrypt(Materials.EncryptionMaterials materials);
    Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>> OnDecrypt(Materials.DecryptionMaterials materials, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys);
  }
  public class _Companion_Keyring {
  }

} // end of namespace KeyringDefs
namespace AwsKmsMrkAwareSymmetricKeyringDef {














  public partial class AwsKmsMrkAwareSymmetricKeyring : KeyringDefs.Keyring {
    public AwsKmsMrkAwareSymmetricKeyring() {
      this._client = default(Amazon.KeyManagementService.IAmazonKeyManagementService);
      this._awsKmsKey = default(Dafny.ISequence<char>);
      this._awsKmsArn = default(AwsKmsArnParsing_Compile.AwsKmsIdentifier);
      this._grantTokens = Dafny.Sequence<Dafny.ISequence<char>>.Empty;
    }
    public void __ctor(Amazon.KeyManagementService.IAmazonKeyManagementService client, Dafny.ISequence<char> awsKmsKey, Dafny.ISequence<Dafny.ISequence<char>> grantTokens)
    {
      Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsKmsIdentifier, Dafny.ISequence<char>> _14599_parsedAwsKmsId;
      _14599_parsedAwsKmsId = AwsKmsArnParsing_Compile.__default.ParseAwsKmsIdentifier(awsKmsKey);
      (this)._client = client;
      (this)._awsKmsKey = awsKmsKey;
      (this)._awsKmsArn = (_14599_parsedAwsKmsId).dtor_value;
      (this)._grantTokens = grantTokens;
    }
    public Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>> OnEncrypt(Materials.EncryptionMaterials materials)
    {
      Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>>.Default(Materials.ValidEncryptionMaterials.Default());
      if (((materials).dtor_plaintextDataKey).is_None) {
        KMSUtils.GenerateDataKeyRequest _14600_generatorRequest;
        _14600_generatorRequest = @KMSUtils.GenerateDataKeyRequest.create((materials).dtor_encryptionContext, (this).grantTokens, (this).awsKmsKey, (int)(AlgorithmSuite.ID.KDFInputKeyLength((materials).dtor_algorithmSuiteID)));
        Wrappers_Compile.Result<KMSUtils.GenerateDataKeyResponse, Dafny.ISequence<char>> _14601_maybeGenerateResponse;
        Wrappers_Compile.Result<KMSUtils.GenerateDataKeyResponse, Dafny.ISequence<char>> _out159;
        _out159 = KMSUtils.ClientHelper.GenerateDataKey((this).client, _14600_generatorRequest);
        _14601_maybeGenerateResponse = _out159;
        if ((_14601_maybeGenerateResponse).is_Failure) {
          res = @Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>>.create_Failure((_14601_maybeGenerateResponse).dtor_error);
          return res;
        }
        KMSUtils.GenerateDataKeyResponse _14602_generateResponse;
        _14602_generateResponse = (_14601_maybeGenerateResponse).dtor_value;
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14603_valueOrError0 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14603_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_14602_generateResponse).IsWellFormed(), Dafny.Sequence<char>.FromString("Invalid response from KMS GenerateDataKey"));
        if ((_14603_valueOrError0).IsFailure()) {
          res = (_14603_valueOrError0).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14604_valueOrError1 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14604_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((AwsKmsArnParsing_Compile.__default.ParseAwsKmsIdentifier((_14602_generateResponse).dtor_keyID)).is_Success, Dafny.Sequence<char>.FromString("Invalid response from KMS GenerateDataKey:: Invalid Key Id"));
        if ((_14604_valueOrError1).IsFailure()) {
          res = (_14604_valueOrError1).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14605_valueOrError2 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14605_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(AlgorithmSuite.ID.ValidPlaintextDataKey((materials).dtor_algorithmSuiteID, (_14602_generateResponse).dtor_plaintext), Dafny.Sequence<char>.FromString("Invalid response from AWS KMS GenerateDataKey: Invalid data key"));
        if ((_14605_valueOrError2).IsFailure()) {
          res = (_14605_valueOrError2).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Dafny.ISequence<byte> _14606_providerInfo = UTF8.ValidUTF8Bytes.Default();
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14607_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out160;
        _out160 = UTF8.__default.Encode((_14602_generateResponse).dtor_keyID);
        _14607_valueOrError3 = _out160;
        if ((_14607_valueOrError3).IsFailure()) {
          res = (_14607_valueOrError3).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        _14606_providerInfo = (_14607_valueOrError3).Extract();
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14608_valueOrError4 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14608_valueOrError4 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((new BigInteger((_14606_providerInfo).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT), Dafny.Sequence<char>.FromString("AWS KMS Key ID too long."));
        if ((_14608_valueOrError4).IsFailure()) {
          res = (_14608_valueOrError4).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Materials.EncryptedDataKey _14609_edk;
        _14609_edk = @Materials.EncryptedDataKey.create(Constants_Compile.__default.PROVIDER__ID, _14606_providerInfo, (_14602_generateResponse).dtor_ciphertextBlob);
        Dafny.ISequence<byte> _14610_plaintextDataKey;
        _14610_plaintextDataKey = (_14602_generateResponse).dtor_plaintext;
        Materials.EncryptionMaterials _14611_result;
        _14611_result = (materials).WithKeys(@Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_14610_plaintextDataKey), Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_14609_edk));
        res = @Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>>.create_Success(_14611_result);
        return res;
      } else {
        KMSUtils.EncryptRequest _14612_encryptRequest;
        _14612_encryptRequest = @KMSUtils.EncryptRequest.create((materials).dtor_encryptionContext, (this).grantTokens, (this).awsKmsKey, ((materials).dtor_plaintextDataKey).dtor_value);
        Wrappers_Compile.Result<KMSUtils.EncryptResponse, Dafny.ISequence<char>> _14613_maybeEncryptResponse;
        Wrappers_Compile.Result<KMSUtils.EncryptResponse, Dafny.ISequence<char>> _out161;
        _out161 = KMSUtils.ClientHelper.Encrypt((this).client, _14612_encryptRequest);
        _14613_maybeEncryptResponse = _out161;
        if ((_14613_maybeEncryptResponse).is_Failure) {
          res = @Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>>.create_Failure((_14613_maybeEncryptResponse).dtor_error);
          return res;
        }
        KMSUtils.EncryptResponse _14614_encryptResponse;
        _14614_encryptResponse = (_14613_maybeEncryptResponse).dtor_value;
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14615_valueOrError5 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14615_valueOrError5 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_14614_encryptResponse).IsWellFormed(), Dafny.Sequence<char>.FromString("Invalid response from KMS Encrypt"));
        if ((_14615_valueOrError5).IsFailure()) {
          res = (_14615_valueOrError5).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14616_valueOrError6 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14616_valueOrError6 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((AwsKmsArnParsing_Compile.__default.ParseAwsKmsIdentifier((_14614_encryptResponse).dtor_keyID)).is_Success, Dafny.Sequence<char>.FromString("Invalid response from AWS KMS Encrypt:: Invalid Key Id"));
        if ((_14616_valueOrError6).IsFailure()) {
          res = (_14616_valueOrError6).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Dafny.ISequence<byte> _14617_providerInfo = UTF8.ValidUTF8Bytes.Default();
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _14618_valueOrError7 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
        Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out162;
        _out162 = UTF8.__default.Encode((_14614_encryptResponse).dtor_keyID);
        _14618_valueOrError7 = _out162;
        if ((_14618_valueOrError7).IsFailure()) {
          res = (_14618_valueOrError7).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        _14617_providerInfo = (_14618_valueOrError7).Extract();
        Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14619_valueOrError8 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
        _14619_valueOrError8 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((new BigInteger((_14617_providerInfo).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT), Dafny.Sequence<char>.FromString("AWS KMS Key ID too long."));
        if ((_14619_valueOrError8).IsFailure()) {
          res = (_14619_valueOrError8).PropagateFailure<Materials.EncryptionMaterials>();
          return res;
        }
        Materials.EncryptedDataKey _14620_edk;
        _14620_edk = @Materials.EncryptedDataKey.create(Constants_Compile.__default.PROVIDER__ID, _14617_providerInfo, (_14614_encryptResponse).dtor_ciphertextBlob);
        Materials.EncryptionMaterials _14621_result;
        _14621_result = (materials).WithKeys((materials).dtor_plaintextDataKey, Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_14620_edk));
        res = @Wrappers_Compile.Result<Materials.EncryptionMaterials, Dafny.ISequence<char>>.create_Success(_14621_result);
        return res;
      }
      return res;
    }
    public Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>> OnDecrypt(Materials.DecryptionMaterials materials, Dafny.ISequence<Materials.EncryptedDataKey> encryptedDataKeys)
    {
      Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.Default(Materials.ValidDecryptionMaterials.Default());
      if (((materials).dtor_plaintextDataKey).is_Some) {
        res = @Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.create_Success(materials);
        return res;
      }
      AwsKmsMrkAwareSymmetricKeyringDef.OnDecryptEncryptedDataKeyFilter _14622_filter;
      AwsKmsMrkAwareSymmetricKeyringDef.OnDecryptEncryptedDataKeyFilter _nw15 = new AwsKmsMrkAwareSymmetricKeyringDef.OnDecryptEncryptedDataKeyFilter();
      _nw15.__ctor((this).awsKmsArn);
      _14622_filter = _nw15;
      Dafny.ISequence<Materials.EncryptedDataKey> _14623_edksToAttempt = Dafny.Sequence<Materials.EncryptedDataKey>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<Materials.EncryptedDataKey>, Dafny.ISequence<char>> _14624_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<Materials.EncryptedDataKey>, Dafny.ISequence<char>>.Default(Dafny.Sequence<Materials.EncryptedDataKey>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<Materials.EncryptedDataKey>, Dafny.ISequence<char>> _out163;
      _out163 = Actions_Compile.__default.FilterWithResult<Materials.EncryptedDataKey, Dafny.ISequence<char>>(_14622_filter, encryptedDataKeys);
      _14624_valueOrError0 = _out163;
      if ((_14624_valueOrError0).IsFailure()) {
        res = (_14624_valueOrError0).PropagateFailure<Materials.DecryptionMaterials>();
        return res;
      }
      _14623_edksToAttempt = (_14624_valueOrError0).Extract();
      AwsKmsMrkAwareSymmetricKeyringDef.DecryptSingleEncryptedDataKey _14625_decryptClosure;
      AwsKmsMrkAwareSymmetricKeyringDef.DecryptSingleEncryptedDataKey _nw16 = new AwsKmsMrkAwareSymmetricKeyringDef.DecryptSingleEncryptedDataKey();
      _nw16.__ctor(materials, (this).client, (this).awsKmsKey, (this).grantTokens);
      _14625_decryptClosure = _nw16;
      Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<Dafny.ISequence<char>>> _14626_outcome;
      Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<Dafny.ISequence<char>>> _out164;
      _out164 = Actions_Compile.__default.ReduceToSuccess<Materials.EncryptedDataKey, Materials.DecryptionMaterials, Dafny.ISequence<char>>(_14625_decryptClosure, _14623_edksToAttempt);
      _14626_outcome = _out164;
      res = ((System.Func<Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<Dafny.ISequence<char>>>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>)((_source28) => {
        if (_source28.is_Success) {
          Materials.DecryptionMaterials _14627___mcc_h0 = ((Wrappers_Compile.Result_Success<Materials.DecryptionMaterials, Dafny.ISequence<Dafny.ISequence<char>>>)_source28).@value;
          return Dafny.Helpers.Let<Materials.DecryptionMaterials, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_14627___mcc_h0, _pat_let8_0 => Dafny.Helpers.Let<Materials.DecryptionMaterials, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_pat_let8_0, _14628_mat => @Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.create_Success(_14628_mat)));
        } else {
          Dafny.ISequence<Dafny.ISequence<char>> _14629___mcc_h1 = ((Wrappers_Compile.Result_Failure<Materials.DecryptionMaterials, Dafny.ISequence<Dafny.ISequence<char>>>)_source28).error;
          return Dafny.Helpers.Let<Dafny.ISequence<Dafny.ISequence<char>>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_14629___mcc_h1, _pat_let9_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.ISequence<char>>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_pat_let9_0, _14630_errors => (((new BigInteger((_14630_errors).Count)).Sign == 0) ? (@Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Unable to decrypt data key: No Encrypted Data Keys found to match."))) : (Dafny.Helpers.Let<Func<Dafny.ISequence<char>, Dafny.ISequence<char>, Dafny.ISequence<char>>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(((System.Func<Dafny.ISequence<char>, Dafny.ISequence<char>, Dafny.ISequence<char>>)((_14631_s, _14632_a) => {
            return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(_14632_a, Dafny.Sequence<char>.FromString("\n")), _14631_s);
          })), _pat_let10_0 => Dafny.Helpers.Let<Func<Dafny.ISequence<char>, Dafny.ISequence<char>, Dafny.ISequence<char>>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_pat_let10_0, _14633_concatString => Dafny.Helpers.Let<Dafny.ISequence<char>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(Seq_Compile.__default.FoldRight<Dafny.ISequence<char>, Dafny.ISequence<char>>(_14633_concatString, _14630_errors, Dafny.Sequence<char>.FromString("Unable to decrypt data key:\n")), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<char>, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>>(_pat_let11_0, _14634_error => @Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.create_Failure(_14634_error)))))))));
        }
      }))(_14626_outcome);
      return res;
      return res;
    }
    public Amazon.KeyManagementService.IAmazonKeyManagementService _client;public Amazon.KeyManagementService.IAmazonKeyManagementService client { get {
      return this._client;
    } }
    public Dafny.ISequence<char> _awsKmsKey;public Dafny.ISequence<char> awsKmsKey { get {
      return this._awsKmsKey;
    } }
    public AwsKmsArnParsing_Compile.AwsKmsIdentifier _awsKmsArn;public AwsKmsArnParsing_Compile.AwsKmsIdentifier awsKmsArn { get {
      return this._awsKmsArn;
    } }
    public Dafny.ISequence<Dafny.ISequence<char>> _grantTokens;public Dafny.ISequence<Dafny.ISequence<char>> grantTokens { get {
      return this._grantTokens;
    } }
  }

  public partial class OnDecryptEncryptedDataKeyFilter : Actions_Compile.ActionWithResult<Materials.EncryptedDataKey, bool, Dafny.ISequence<char>>, Actions_Compile.Action<Materials.EncryptedDataKey, Wrappers_Compile.Result<bool, Dafny.ISequence<char>>> {
    public OnDecryptEncryptedDataKeyFilter() {
      this._awsKmsKey = default(AwsKmsArnParsing_Compile.AwsKmsIdentifier);
    }
    public void __ctor(AwsKmsArnParsing_Compile.AwsKmsIdentifier awsKmsKey)
    {
      (this)._awsKmsKey = awsKmsKey;
    }
    public Wrappers_Compile.Result<bool, Dafny.ISequence<char>> Invoke(Materials.EncryptedDataKey edk)
    {
      Wrappers_Compile.Result<bool, Dafny.ISequence<char>> res = Wrappers_Compile.Result<bool, Dafny.ISequence<char>>.Default(false);
      if (!((edk).dtor_providerID).Equals((Constants_Compile.__default.PROVIDER__ID))) {
        res = @Wrappers_Compile.Result<bool, Dafny.ISequence<char>>.create_Success(false);
        return res;
      }
      if (!(UTF8.__default.ValidUTF8Seq((edk).dtor_providerInfo))) {
        res = @Wrappers_Compile.Result<bool, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Invalid AWS KMS encoding, provider info is not UTF8."));
        return res;
      }
      Dafny.ISequence<char> _14635_keyId = Dafny.Sequence<char>.Empty;
      Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>> _14636_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>> _out165;
      _out165 = UTF8.__default.Decode((edk).dtor_providerInfo);
      _14636_valueOrError0 = _out165;
      if ((_14636_valueOrError0).IsFailure()) {
        res = (_14636_valueOrError0).PropagateFailure<bool>();
        return res;
      }
      _14635_keyId = (_14636_valueOrError0).Extract();
      AwsKmsArnParsing_Compile.AwsArn _14637_arn = AwsKmsArnParsing_Compile.AwsArn.Default();
      Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsArn, Dafny.ISequence<char>> _14638_valueOrError1 = Wrappers_Compile.Result<AwsKmsArnParsing_Compile.AwsArn, Dafny.ISequence<char>>.Default(AwsKmsArnParsing_Compile.AwsArn.Default());
      _14638_valueOrError1 = AwsKmsArnParsing_Compile.__default.ParseAwsKmsArn(_14635_keyId);
      if ((_14638_valueOrError1).IsFailure()) {
        res = (_14638_valueOrError1).PropagateFailure<bool>();
        return res;
      }
      _14637_arn = (_14638_valueOrError1).Extract();
      res = @Wrappers_Compile.Result<bool, Dafny.ISequence<char>>.create_Success(AwsKmsMrkMatchForDecrypt_Compile.__default.AwsKmsMrkMatchForDecrypt((this).awsKmsKey, @AwsKmsArnParsing_Compile.AwsKmsIdentifier.create_AwsKmsArnIdentifier(_14637_arn)));
      return res;
      return res;
    }
    public AwsKmsArnParsing_Compile.AwsKmsIdentifier _awsKmsKey;public AwsKmsArnParsing_Compile.AwsKmsIdentifier awsKmsKey { get {
      return this._awsKmsKey;
    } }
  }

  public partial class DecryptSingleEncryptedDataKey : Actions_Compile.ActionWithResult<Materials.EncryptedDataKey, Materials.DecryptionMaterials, Dafny.ISequence<char>>, Actions_Compile.Action<Materials.EncryptedDataKey, Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>> {
    public DecryptSingleEncryptedDataKey() {
      this._materials = default(Materials.DecryptionMaterials);
      this._client = default(Amazon.KeyManagementService.IAmazonKeyManagementService);
      this._awsKmsKey = default(Dafny.ISequence<char>);
      this._grantTokens = Dafny.Sequence<Dafny.ISequence<char>>.Empty;
    }
    public void __ctor(Materials.DecryptionMaterials materials, Amazon.KeyManagementService.IAmazonKeyManagementService client, Dafny.ISequence<char> awsKmsKey, Dafny.ISequence<Dafny.ISequence<char>> grantTokens)
    {
      (this)._materials = materials;
      (this)._client = client;
      (this)._awsKmsKey = awsKmsKey;
      (this)._grantTokens = grantTokens;
    }
    public Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>> Invoke(Materials.EncryptedDataKey edk)
    {
      Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>> res = default(Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>);
      KMSUtils.DecryptRequest _14639_decryptRequest;
      _14639_decryptRequest = @KMSUtils.DecryptRequest.create((this).awsKmsKey, (edk).dtor_ciphertext, ((this).materials).dtor_encryptionContext, (this).grantTokens);
      KMSUtils.DecryptResponse _14640_decryptResponse = KMSUtils.DecryptResponse.Default();
      Wrappers_Compile.Result<KMSUtils.DecryptResponse, Dafny.ISequence<char>> _14641_valueOrError0 = Wrappers_Compile.Result<KMSUtils.DecryptResponse, Dafny.ISequence<char>>.Default(KMSUtils.DecryptResponse.Default());
      Wrappers_Compile.Result<KMSUtils.DecryptResponse, Dafny.ISequence<char>> _out166;
      _out166 = KMSUtils.ClientHelper.Decrypt((this).client, _14639_decryptRequest);
      _14641_valueOrError0 = _out166;
      if ((_14641_valueOrError0).IsFailure()) {
        res = (_14641_valueOrError0).PropagateFailure<Materials.DecryptionMaterials>();
        return res;
      }
      _14640_decryptResponse = (_14641_valueOrError0).Extract();
      Wrappers_Compile.Outcome<Dafny.ISequence<char>> _14642_valueOrError1 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _14642_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((((_14640_decryptResponse).dtor_keyID).Equals(((this).awsKmsKey))) && (AlgorithmSuite.ID.ValidPlaintextDataKey(((this).materials).dtor_algorithmSuiteID, (_14640_decryptResponse).dtor_plaintext)), Dafny.Sequence<char>.FromString("Invalid response from KMS Decrypt"));
      if ((_14642_valueOrError1).IsFailure()) {
        res = (_14642_valueOrError1).PropagateFailure<Materials.DecryptionMaterials>();
        return res;
      }
      Materials.DecryptionMaterials _14643_result;
      _14643_result = ((this).materials).WithPlaintextDataKey((_14640_decryptResponse).dtor_plaintext);
      res = @Wrappers_Compile.Result<Materials.DecryptionMaterials, Dafny.ISequence<char>>.create_Success(_14643_result);
      return res;
      return res;
    }
    public Materials.DecryptionMaterials _materials;public Materials.DecryptionMaterials materials { get {
      return this._materials;
    } }
    public Amazon.KeyManagementService.IAmazonKeyManagementService _client;public Amazon.KeyManagementService.IAmazonKeyManagementService client { get {
      return this._client;
    } }
    public Dafny.ISequence<char> _awsKmsKey;public Dafny.ISequence<char> awsKmsKey { get {
      return this._awsKmsKey;
    } }
    public Dafny.ISequence<Dafny.ISequence<char>> _grantTokens;public Dafny.ISequence<Dafny.ISequence<char>> grantTokens { get {
      return this._grantTokens;
    } }
  }

} // end of namespace AwsKmsMrkAwareSymmetricKeyringDef
namespace Base64Lemmas_Compile {





} // end of namespace Base64Lemmas_Compile
namespace Sorting_Compile {




  public partial class __default {
    public static bool LexicographicByteSeqBelow(Dafny.ISequence<byte> x, Dafny.ISequence<byte> y)
    {
      return Sorting_Compile.__default.LexicographicByteSeqBelowAux(x, y, BigInteger.Zero);
    }
    public static bool LexicographicByteSeqBelowAux(Dafny.ISequence<byte> x, Dafny.ISequence<byte> y, BigInteger n)
    {
      return (((n) == (new BigInteger((x).Count))) || (((n) != (new BigInteger((y).Count))) && (((x).Select(n)) < ((y).Select(n))))) || ((((n) != (new BigInteger((y).Count))) && (((x).Select(n)) == ((y).Select(n)))) && (Sorting_Compile.__default.LexicographicByteSeqBelowAux(x, y, (n) + (BigInteger.One))));
    }
    public static void SelectionSort<__Data>(__Data[] a, Func<__Data, __Data, bool> below)
    {
      BigInteger _14644_m;
      _14644_m = BigInteger.Zero;
      while ((_14644_m) < (new BigInteger((a).Length))) {
        BigInteger _14645_mindex;
        BigInteger _14646_n;
        BigInteger _rhs13 = _14644_m;
        BigInteger _rhs14 = (_14644_m) + (BigInteger.One);
        _14645_mindex = _rhs13;
        _14646_n = _rhs14;
        while ((_14646_n) < (new BigInteger((a).Length))) {
          if (!(Dafny.Helpers.Id<Func<__Data, __Data, bool>>(below)((a)[(int)(_14645_mindex)], (a)[(int)(_14646_n)]))) {
            _14645_mindex = _14646_n;
          }
          _14646_n = (_14646_n) + (BigInteger.One);
        }
        __Data _rhs15 = (a)[(int)(_14645_mindex)];
        __Data _rhs16 = (a)[(int)(_14644_m)];
        __Data[] _lhs0 = a;
        BigInteger _lhs1 = _14644_m;
        __Data[] _lhs2 = a;
        BigInteger _lhs3 = _14645_mindex;
        _lhs0[(int)(_lhs1)] = _rhs15;
        _lhs2[(int)(_lhs3)] = _rhs16;
        _14644_m = (_14644_m) + (BigInteger.One);
      }
    }
  }
} // end of namespace Sorting_Compile
namespace Time_Compile {



} // end of namespace Time_Compile
namespace _module {














































} // end of namespace _module
