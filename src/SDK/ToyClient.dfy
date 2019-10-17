include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "AlgorithmSuite.dfy"
include "CMM/Defs.dfy"
include "CMM/DefaultCMM.dfy"
include "Keyring/Defs.dfy"
include "Materials.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/EncryptionParameters.dfy"
include "../Crypto/Random.dfy"

module ToyClientDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMMDefs
  import DefaultCMMDef
  import KeyringDefs
  import Random
  import AlgorithmSuite
  import AESEncryption
  import EncryptionParameters

  datatype Encryption = Encryption(ec: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>, iv: seq<uint8>, ctxt: seq<uint8>, authTag: seq<uint8>)

  const ALGORITHM := EncryptionParameters.AES_GCM_256

  class Client {
    var cmm: CMMDefs.CMM
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      cmm in Repr && cmm.Repr <= Repr && this !in cmm.Repr && cmm.Valid()
    }

    constructor OfCMM(c: CMMDefs.CMM) requires c.Valid() ensures Valid() {
      cmm := c;
      Repr := {this, cmm} + c.Repr;
    }

    constructor OfKeyring(k: KeyringDefs.Keyring)
      requires k.Valid()
      ensures Valid()
      ensures fresh(cmm)
    {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(k);
      new;
      Repr := {this, cmm} + cmm.Repr;
    }

    method GetEncMaterials(ec: Materials.EncryptionContext) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID == AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
    {
      var r :- cmm.GetEncryptionMaterials(ec, None, None);
      if r.algorithmSuiteID != AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 {
        return Failure("bad alg id");
      } else if r.plaintextDataKey.None? {
        return Failure("bad data key");
      }
      return Success(r);
    }

    method Encrypt(pt: seq<uint8>, ec: Materials.EncryptionContext) returns (res: Result<Encryption>)
      requires Valid()
      ensures Valid()
    {
      var em :- GetEncMaterials(ec);
      if |em.plaintextDataKey.get| != 32 {
        return Failure("bad data key length");
      }
      var iv := Random.GenerateBytes(ALGORITHM.ivLen as int32);
      var ciphertext :- AESEncryption.AESEncrypt(ALGORITHM, iv ,em.plaintextDataKey.get, pt, []);
      return Success(Encryption(em.encryptionContext, em.encryptedDataKeys, iv, ciphertext.cipherText, ciphertext.authTag));
    }

    method Decrypt(e: Encryption) returns (res: Result<seq<uint8>>)
      requires Valid()
      requires ALGORITHM.tagLen as int == |e.authTag|
      requires ALGORITHM.ivLen as int == |e.iv|
      ensures Valid()
    {
      if |e.edks| == 0 {
        return Failure("no edks");
      }
      var decmat :- cmm.DecryptMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, e.edks, e.ec);
      match decmat.plaintextDataKey
      case Some(dk) =>
        if |dk| == 32 {
          var msg := AESEncryption.AESDecrypt(ALGORITHM, dk, e.ctxt, e.authTag, e.iv, []);
          return msg;
        } else {
          return Failure("bad dk");
        }
      case None =>
        return Failure("no dk?");
    }
  }
}
