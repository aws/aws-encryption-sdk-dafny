include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"

module RSAKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KeyringDefs
  import AlgorithmSuite
  import RSA = RSAEncryption
  import Materials
  import Random

  class RSAKeyring extends KeyringDefs.Keyring {
    const keyNamespace: seq<uint8>
    const keyName: seq<uint8>
    const paddingMode: RSA.RSAPaddingMode
    const bitLength: RSA.RSABitLength
    const encryptionKey: Option<seq<uint8>>
    const decryptionKey: Option<seq<uint8>>

    predicate Valid()
      reads this
    {
      Repr == {this} &&
      (encryptionKey.Some? ==> RSA.RSA.RSAWfEK(bitLength, paddingMode, encryptionKey.get)) &&
      (decryptionKey.Some? ==> RSA.RSA.RSAWfDK(bitLength, paddingMode, decryptionKey.get)) &&
      (encryptionKey.Some? || decryptionKey.Some?)
    }

    constructor(namespace: seq<uint8>, name: seq<uint8>, padding: RSA.RSAPaddingMode, bits: RSA.RSABitLength, ek: Option<seq<uint8>>, dk: Option<seq<uint8>>)
      requires ek.Some? ==> RSA.RSA.RSAWfEK(bits, padding, ek.get)
      requires dk.Some? ==> RSA.RSA.RSAWfDK(bits, padding, dk.get)
      requires ek.Some? || dk.Some?
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures paddingMode == padding && bitLength == bits
      ensures encryptionKey == ek
      ensures decryptionKey == dk
      ensures Valid()
    {
      keyNamespace := namespace;
      keyName := name;
      paddingMode, bitLength := padding, bits;
      encryptionKey := ek;
      decryptionKey := dk;
      Repr := {this};
    }

    method OnEncrypt(encMat: Materials.ValidEncryptionMaterialsInput) returns (res: Result<Option<Materials.ValidDataKey>>)
      requires Valid()
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==> 
        encMat.algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? ==> 
        (encMat.plaintextDataKey.Some? ==> encMat.plaintextDataKey.get == res.value.get.plaintextDataKey)
    {
      if encryptionKey.None? {
        return Failure("Encryption key undefined");
      } else {
        var plaintextDataKey := encMat.plaintextDataKey;
        var algorithmID := encMat.algorithmSuiteID;
        if plaintextDataKey.None? {
          var k := Random.GenerateBytes(algorithmID.KeyLength() as int32);
          plaintextDataKey := Some(k);
        }
        var aad := Materials.FlattenSortEncCtx(encMat.encryptionContext);
        var edkCiphertext := RSA.RSA.RSAEncrypt(bitLength, paddingMode, encryptionKey.get, plaintextDataKey.get);
        if edkCiphertext.None? {
          return Failure("Error on encrypt!");
        }
        var edk := Materials.EncryptedDataKey(ByteSeqToString(keyNamespace), keyName, edkCiphertext.get);
        var dataKey := Materials.DataKey(encMat.algorithmSuiteID, plaintextDataKey.get, [edk]);
        assert dataKey.algorithmSuiteID.ValidPlaintextDataKey(dataKey.plaintextDataKey);
        return Success(Some(dataKey));
      }
    }

    method OnDecrypt(decMat: Materials.DecryptionMaterials, edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey
      ensures Valid()
      ensures decMat.Valid()
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
    {
      if decMat.plaintextDataKey.Some? || |edks| == 0 {
        return Success(decMat);
      } else if decryptionKey.None? {
        return Failure("Decryption key undefined");
      }
      var i := 0;
      while i < |edks|
        invariant  0 <= i <= |edks|
      {
        var edk := edks[i];
        if edk.providerID != ByteSeqToString(keyNamespace) {
          // continue with the next EDK
        } else if edk.providerInfo != keyName {
          // continue with the next EDK
        } else {
          var octxt := RSA.RSA.RSADecrypt(bitLength, paddingMode, decryptionKey.get, edks[0].ciphertext);
          match octxt
          case None =>
            // continue with the next EDK
          case Some(k) =>
            if |k| == decMat.algorithmSuiteID.KeyLength() { // check for correct key length
              decMat.plaintextDataKey := Some(k);
              return Success(decMat);
            } else {
              return Failure(("Bad key length!"));
            }
        }
        i := i + 1;
      }
      return Success(decMat);
    }
  }
}
