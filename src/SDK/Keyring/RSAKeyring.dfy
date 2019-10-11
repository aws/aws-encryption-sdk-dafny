include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../../Crypto/GenBytes.dfy"
include "../../Crypto/RSAEncryption.dfy"

module RSAKeyringDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import KeyringDefs
  import AlgorithmSuite
  import RSA = RSAEncryption
  import Materials
  import RNG

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

    method OnEncrypt(encMat: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      requires encMat.Valid()
      modifies encMat`plaintextDataKey, encMat`encryptedDataKeys, encMat`keyringTrace
      ensures Valid()
      ensures res.Success? ==> res.value.Valid() && res.value == encMat
      ensures res.Success? && old(encMat.plaintextDataKey.Some?) ==> res.value.plaintextDataKey == old(encMat.plaintextDataKey)
      ensures res.Failure? ==> unchanged(encMat)
      // Iff keyring set plaintext data key on encrypt, keyring trace contains a new trace with the GENERATED_DATA_KEY flag.
      ensures old(encMat.plaintextDataKey).None? && encMat.plaintextDataKey.Some? <==>
        |encMat.keyringTrace| > |old(encMat.keyringTrace)| &&
        exists trace :: trace in encMat.keyringTrace[|old(encMat.keyringTrace)|..] && Materials.GENERATED_DATA_KEY in trace.flags
      // Iff keyring added a new encryptedDataKey, keyring trace contains a new trace with the ENCRYPTED_DATA_KEY flag.
      ensures |encMat.encryptedDataKeys| > |old(encMat.encryptedDataKeys)| <==>
        |encMat.keyringTrace| > |old(encMat.keyringTrace)| &&
        exists trace :: trace in encMat.keyringTrace[|old(encMat.keyringTrace)|..] && Materials.ENCRYPTED_DATA_KEY in trace.flags
    {
      if encryptionKey.None? {
        res := Failure("Encryption key undefined");
      } else {
        var dataKey := encMat.plaintextDataKey;
        var algorithmID := encMat.algorithmSuiteID;
        if dataKey.None? {
          var k := RNG.GenBytes(algorithmID.KeyLength() as uint16);
          dataKey := Some(k);
        }
        var aad := Materials.FlattenSortEncCtx(encMat.encryptionContext);
        var edkCiphertext := RSA.RSA.RSAEncrypt(bitLength, paddingMode, encryptionKey.get, dataKey.get);
        if edkCiphertext.None? {
          return Failure("Error on encrypt!");
        }

        if encMat.plaintextDataKey.None? {
          var generateTrace := Materials.KeyringTraceEntry(ByteSeqToString(keyNamespace), ByteSeqToString(keyName), {Materials.GENERATED_DATA_KEY});
          encMat.SetPlaintextDataKey(dataKey.get, generateTrace);
        }

        var edk := Materials.EncryptedDataKey(ByteSeqToString(keyNamespace), keyName, edkCiphertext.get);
        var encryptTrace := Materials.KeyringTraceEntry(ByteSeqToString(keyNamespace), ByteSeqToString(keyName), {Materials.ENCRYPTED_DATA_KEY});
        encMat.AppendEncryptedDataKey(edk, encryptTrace);

        return Success(encMat);
      }
    }

    method OnDecrypt(decMat: Materials.DecryptionMaterials, edks: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      requires decMat.Valid()
      modifies decMat`plaintextDataKey, decMat`keyringTrace
      ensures Valid()
      ensures decMat.Valid()
      ensures |edks| == 0 ==> res.Success? && unchanged(decMat)
      ensures old(decMat.plaintextDataKey.Some?) ==> res.Success? && unchanged(decMat)
      ensures res.Success? ==> res.value == decMat
      ensures res.Failure? ==> unchanged(decMat)
      // Iff keyring set plaintext data key on decrypt, keyring trace contains a new trace with the DECRYPTED_DATA_KEY flag.
      ensures old(decMat.plaintextDataKey).None? && decMat.plaintextDataKey.Some? <==>
        |decMat.keyringTrace| > |old(decMat.keyringTrace)| &&
        decMat.keyringTrace[..|old(decMat.keyringTrace)|] == old(decMat.keyringTrace) &&
        exists trace :: trace in decMat.keyringTrace[|old(decMat.keyringTrace)|..] &&
        Materials.DECRYPTED_DATA_KEY in trace.flags
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
              var decryptTrace := Materials.KeyringTraceEntry(ByteSeqToString(keyNamespace), ByteSeqToString(keyName), {Materials.DECRYPTED_DATA_KEY});
              decMat.SetPlaintextDataKey(k, decryptTrace);
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
