include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "../Materials.dfy"
include "../AlgorithmSuite.dfy"

module {:extern "KeyringDefs"} KeyringDefs {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import AlgorithmSuite

  trait {:termination false} Keyring {
    ghost const Repr : set<object>
    predicate Valid()

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID 
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
      decreases Repr

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && res.value.verificationKey == materials.verificationKey
      decreases Repr
  }
 
  type ValidKeyring? = k: Keyring? | k == null || k.Valid()

  trait {:extern "AWSEncryptionSDK.Keyring"} ExternalKeyring {

    ghost const Repr: set<object>

    method OnEncrypt(materials: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      // TODO-RS: Unsound!
      requires materials.Valid()
      decreases Repr

    method OnDecrypt(materials: Materials.DecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      // TODO-RS: Unsound!
      requires materials.Valid()
      decreases Repr
  }

  class AsExternalKeyring extends ExternalKeyring {
    const wrapped: ValidKeyring?;
    constructor(wrapped: ValidKeyring?) 
        requires wrapped != null
    {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }

    predicate Valid() {
        && this in Repr 
        && wrapped in Repr 
        && wrapped.Repr <= Repr 
        && this !in wrapped.Repr
    }
    lemma AlwaysValid(k: AsExternalKeyring) ensures k.Valid()    

    method OnEncrypt(materials: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires materials.Valid()
      decreases Repr
    {
      AlwaysValid(this);
      res := wrapped.OnEncrypt(materials);
    }

    method OnDecrypt(materials: Materials.DecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires materials.Valid()
      decreases Repr
    {
      AlwaysValid(this);
      res := wrapped.OnDecrypt(materials, encryptedDataKeys);
    }
  }

  class AsKeyring extends Keyring {
    const wrapped: ExternalKeyring;

    constructor(wrapped: ExternalKeyring) {
      this.wrapped := wrapped;
    }

    predicate Valid() {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
    }
    lemma AlwaysValid(k: AsKeyring) ensures k.Valid()

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID 
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
      decreases Repr
    {
      AlwaysValid(this);
      var result := wrapped.OnEncrypt(materials);
      var _ :- FailUnless(result.Success? ==> result.value.Valid(), "Invalid result");
      res := result;
      expect res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID 
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey;
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      ensures |encryptedDataKeys| == 0 ==> res.Success? && materials == res.value
      ensures materials.plaintextDataKey.Some? ==> res.Success? && materials == res.value
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && res.value.verificationKey == materials.verificationKey
      decreases Repr
    {
      if |encryptedDataKeys| == 0 || materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      AlwaysValid(this);
      var result := wrapped.OnDecrypt(materials, encryptedDataKeys);
      var _ :- FailUnless(result.Success? ==> result.value.Valid(), "Invalid result");
      res := result;
      expect res.Success? ==>
            && materials.encryptionContext == res.value.encryptionContext
            && materials.algorithmSuiteID == res.value.algorithmSuiteID
            && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
            && materials.keyringTrace <= res.value.keyringTrace
            && res.value.verificationKey == materials.verificationKey;
    }
  }
}
