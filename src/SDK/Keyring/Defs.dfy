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
    ghost const Repr : set<object>;

    predicate Valid()

    method OnEncrypt(materials: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      // TODO-RS: Unsound!
      requires Valid()
      requires materials.Valid()
      decreases Repr

    method OnDecrypt(materials: Materials.DecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      // TODO-RS: Unsound!
      requires Valid()
      requires materials.Valid()
      decreases Repr
  }

  type ValidExternalKeyring? = k: ExternalKeyring? | k == null || k.Valid()

  class AsExternalKeyring extends ExternalKeyring {
    const wrapped: ValidKeyring?;
    constructor(wrapped: ValidKeyring?) 
        requires wrapped != null
        ensures Valid() 
        ensures fresh(Repr - {wrapped} - wrapped.Repr)
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

    method OnEncrypt(materials: Materials.EncryptionMaterials) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      requires materials.Valid()
      decreases Repr
    {
      var _ :- Require(wrapped != null);
      res := wrapped.OnEncrypt(materials);
    }

    method OnDecrypt(materials: Materials.DecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.DecryptionMaterials>)
      requires Valid()
      requires materials.Valid()
      decreases Repr
    {
      var _ :- Require(wrapped != null);
      res := wrapped.OnDecrypt(materials, encryptedDataKeys);
    }
  }

  class AsKeyring extends Keyring {
    const wrapped: ValidExternalKeyring?;

    constructor(wrapped: ValidExternalKeyring?) {
      this.wrapped := wrapped;
    }

    predicate Valid() {
      && this in Repr 
      && wrapped in Repr 
      && wrapped.Repr <= Repr 
      && this !in wrapped.Repr
      && wrapped.Valid()
    }

    method OnEncrypt(materials: Materials.ValidEncryptionMaterials) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      ensures res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID 
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey
      decreases Repr
    {
      var _ :- Require(wrapped != null);
      var result := wrapped.OnEncrypt(materials);
      var _ :- Require(result.Success? ==> result.value.Valid());
      res := result;
      var _ :- Require(res.Success? ==>
          && materials.encryptionContext == res.value.encryptionContext
          && materials.algorithmSuiteID == res.value.algorithmSuiteID 
          && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
          && materials.keyringTrace <= res.value.keyringTrace
          && materials.encryptedDataKeys <= res.value.encryptedDataKeys
          && materials.signingKey == res.value.signingKey);
    }

    method OnDecrypt(materials: Materials.ValidDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
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
      var _ :- Require(wrapped != null);
      var result := wrapped.OnDecrypt(materials, encryptedDataKeys);
      var _ :- Require(result.Success? ==> result.value.Valid());
      res := result;
      var _ :- Require(res.Success? ==>
            && materials.encryptionContext == res.value.encryptionContext
            && materials.algorithmSuiteID == res.value.algorithmSuiteID
            && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
            && materials.keyringTrace <= res.value.keyringTrace
            && res.value.verificationKey == materials.verificationKey);
    }

  }
}
