include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../../Crypto/Random.dfy"
include "../../Crypto/RSAEncryption.dfy"
include "../../Util/UTF8.dfy"

module RawRSAKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KeyringDefs
  import AlgorithmSuite
  import RSA = RSAEncryption
  import Materials
  import Random
  import UTF8

  class RawRSAKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
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

    constructor(namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, padding: RSA.RSAPaddingMode, bits: RSA.RSABitLength, ek: Option<seq<uint8>>, dk: Option<seq<uint8>>)
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

    method OnEncrypt(encMat: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Failure? ==> unchanged(encMat)
    {
      if encryptionKey.None? {
        return Failure("Encryption key undefined");
      } else {
        var dataKey := encMat.plaintextDataKey;
        var algorithmID := encMat.algorithmSuiteID;
        if dataKey.None? {
          var k := Random.GenerateBytes(algorithmID.KeyLength() as int32);
          dataKey := Some(k);
        }
        var aad := Materials.FlattenSortEncCtx(encMat.encryptionContext);
        var edkCiphertext := RSA.RSA.RSAEncrypt(bitLength, paddingMode, encryptionKey.get, dataKey.get);
        if edkCiphertext.None? {
          return Failure("Error on encrypt!");
        }
        var edk := Materials.EncryptedDataKey(keyNamespace, keyName, edkCiphertext.get);
        encMat.encryptedDataKeys := [edk] + encMat.encryptedDataKeys;
        encMat.plaintextDataKey := dataKey;
        return Success(encMat);
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
        if edk.providerID != keyNamespace {
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
