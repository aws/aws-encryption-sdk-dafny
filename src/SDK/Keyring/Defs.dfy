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
      // TODO-RS: Temporary to let everything compile, hoping to not have to do this permanently.
      decreases *

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
      // TODO-RS: Temporary to let everything compile, hoping to not have to do this permanently.
      decreases *
  }
 
  type ValidKeyring? = k: Keyring? | k == null || k.Valid()

  trait {:extern} ExternalKeyring {

    ghost const Repr: set<object>

    method OnEncrypt(materials: Materials.ExternalEncryptionMaterials) returns (res: Result<Materials.ExternalEncryptionMaterials>)
      decreases *

    method OnDecrypt(materials: Materials.ExternalDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ExternalDecryptionMaterials>)
      decreases *
  }

  class AsExternalKeyring extends ExternalKeyring {
    const wrapped: ValidKeyring?;
    constructor(wrapped: ValidKeyring?) 
        requires wrapped != null
        ensures Valid()
    {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }

    predicate Valid() {
        && this in Repr 
        && wrapped != null
        && wrapped in Repr 
        && wrapped.Repr <= Repr 
        && this !in wrapped.Repr
    }

    method OnEncrypt(materials: Materials.ExternalEncryptionMaterials) returns (res: Result<Materials.ExternalEncryptionMaterials>)
      decreases *
    {
      expect wrapped != null;
      var internalMaterials :- wrapped.OnEncrypt(materials.wrapped);
      var externalMaterials := new Materials.ExternalEncryptionMaterials(internalMaterials);
      res := Success(externalMaterials);
    }

    method OnDecrypt(materials: Materials.ExternalDecryptionMaterials,
                     encryptedDataKeys: seq<Materials.EncryptedDataKey>) returns (res: Result<Materials.ExternalDecryptionMaterials>)
      decreases *
    {
      expect wrapped != null;
      var internalMaterials :- wrapped.OnDecrypt(materials.wrapped, encryptedDataKeys);
      var externalMaterials := new Materials.ExternalDecryptionMaterials(internalMaterials);
      res := Success(externalMaterials);
    }
  }

  method ToExternalKeyring(k: ValidKeyring?) returns (res: ExternalKeyring?) 
    ensures k == null <==> res == null 
  {
    if k == null {
      res := null;
    } else {
      var casted := Cast<AsExternalKeyring>(k, _ => true);
      match casted {
        case Some(keyring) => 
          res := keyring;
        case None =>
          res := new AsExternalKeyring(k);
      }
    }
  }

  class AsKeyring extends Keyring {
    const wrapped: ExternalKeyring;

    constructor(wrapped: ExternalKeyring) ensures Valid() {
      this.wrapped := wrapped;
    }

    predicate Valid() {
      true
    }

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
      decreases *
    {
      var externalMaterials := new Materials.ExternalEncryptionMaterials(materials);
      var result :- wrapped.OnEncrypt(externalMaterials);
      res := Success(result.wrapped); // TODO-RS: Exception handling!
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
      decreases *
    {
      if |encryptedDataKeys| == 0 || materials.plaintextDataKey.Some? {
        return Success(materials);
      }
      var externalMaterials := new Materials.ExternalDecryptionMaterials(materials);
      var result :- wrapped.OnDecrypt(externalMaterials, encryptedDataKeys);
      res := Success(result.wrapped);
      expect res.Success? ==>
            && materials.encryptionContext == res.value.encryptionContext
            && materials.algorithmSuiteID == res.value.algorithmSuiteID
            && (materials.plaintextDataKey.Some? ==> res.value.plaintextDataKey == materials.plaintextDataKey)
            && materials.keyringTrace <= res.value.keyringTrace
            && res.value.verificationKey == materials.verificationKey;
    }
  }

  method FromExternalKeyring(k: ExternalKeyring?) returns (res: ValidKeyring?) 
    ensures k == null <==> res == null 
  {
    if k == null {
      res := null;
    } else {
      var casted := Cast<AsKeyring>(k, _ => true);
      match casted {
        case Some(keyring) => 
          assert keyring.Valid();
          res := keyring;
        case None =>
          res := new AsKeyring(k);
      }
    }
  }
}
