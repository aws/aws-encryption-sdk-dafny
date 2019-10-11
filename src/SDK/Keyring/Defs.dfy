include "../../StandardLibrary/StandardLibrary.dfy"
include "../Materials.dfy"

module KeyringDefs {
  import opened StandardLibrary
  import Materials

  trait {:termination false} Keyring {
    ghost var Repr : set<object>
    predicate Valid() reads this, Repr

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
  }
}
