include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Materials.dfy"
include "CMM/Defs.dfy"
include "CMM/DefaultCMM.dfy"
include "Keyring/Defs.dfy"
include "AlgorithmSuite.dfy"
include "../Crypto/AESEncryption.dfy"
include "../Crypto/EncryptionSuites.dfy"
include "../Crypto/Random.dfy"
include "MessageHeader.dfy"

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
  import EncryptionSuites
  import MessageHeader

  datatype Encryption = Encryption(ec: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>, iv: seq<uint8>, ctxt: seq<uint8>, authTag: seq<uint8>)

  const ALGORITHM := EncryptionSuites.AES_GCM_256

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

    method GetEncMaterials(ec: Materials.EncryptionContext) returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires MessageHeader.ValidAAD(ec) && ec.Keys !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> 
        res.value.dataKeyMaterials.algorithmSuiteID == AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
    {
      var r :- cmm.GetEncryptionMaterials(ec, None, None);
      if r.dataKeyMaterials.algorithmSuiteID != AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 {
        return Failure("bad alg id");
      }
      return Success(r);
    }

    method Encrypt(pt: seq<uint8>, ec: Materials.EncryptionContext) returns (res: Result<Encryption>)
      requires Valid()
      requires MessageHeader.ValidAAD(ec) && ec.Keys !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> |res.value.authTag| == ALGORITHM.tagLen as int
      ensures res.Success? ==> |res.value.iv| == ALGORITHM.ivLen as int
    {
      var em :- GetEncMaterials(ec);
      var iv :- Random.GenerateBytes(ALGORITHM.ivLen as int32);
      var ciphertext :- AESEncryption.AESEncrypt(ALGORITHM, iv, em.dataKeyMaterials.plaintextDataKey, pt, []);
      return Success(Encryption(em.encryptionContext, em.dataKeyMaterials.encryptedDataKeys, 
                                iv, ciphertext.cipherText, ciphertext.authTag));
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
      if |decmat.plaintextDataKey| == 32 {
        var msg := AESEncryption.AESDecrypt(ALGORITHM, decmat.plaintextDataKey, e.ctxt, e.authTag, e.iv, []);
        return msg;
      } else {
        return Failure("bad dk");
      }
    }
  }
}
