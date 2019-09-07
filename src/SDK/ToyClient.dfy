include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "Common.dfy"
include "CMM/Defs.dfy"
include "AlgorithmSuite.dfy"
include "../Crypto/AESEncryption.dfy"

module ToyClientDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Materials
  import CMMDefs
  import AlgorithmSuite
  import AESEncryption
  import Cipher

  datatype Encryption = Encryption(ec: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>, ctxt: seq<uint8>)

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

    /*
    constructor OfKeyring(k: Keyring.Keyring) requires k.Valid() ensures Valid() ensures fresh(cmm) {
      cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(k);
      new;
      Repr := {this, cmm} + cmm.Repr;
    }
    */

    method GetEncMaterials(ec: Materials.EncryptionContext) returns (res: Result<Materials.EncryptionMaterials>)
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID == AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384
      ensures res.Success? ==> res.value.plaintextDataKey.Some?
    {
      var rResult := cmm.EncMatRequest(ec, None, None);
      match rResult
      case Failure(err) =>
        return Failure(err);
      case Success(r) =>
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
      var emResult := GetEncMaterials(ec);
      match emResult
      case Failure(err) =>
        return Failure(err);
      case Success(em) =>
        if |em.plaintextDataKey.get| != 32 {
          return Failure("bad data key length");
        }
        var ciphertextResult := AESEncryption.AES.AESEncrypt(Cipher.AES_GCM_256, em.plaintextDataKey.get, pt, []);
        match ciphertextResult
        case Success(ciphertext) =>
          return Success(Encryption(em.encryptionContext, em.encryptedDataKeys, ciphertext));
        case Failure(err) =>
          return Failure(err);
    }

    method Decrypt(e: Encryption) returns (res: Result<seq<uint8>>)
      requires Valid()
      ensures Valid()
    {
      if |e.edks| == 0 {
        return Failure("no edks");
      }
      var decmatResult := cmm.DecMatRequest(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, e.edks, e.ec);
      match decmatResult
      case Failure(err) =>
        return Failure(err);
      case Success(decmat) =>
        match decmat.plaintextDataKey
        case Some(dk) =>
          if |dk| == 32 && |e.ctxt| > 12 {
            var msg := AESEncryption.AES.AESDecrypt(Cipher.AES_GCM_256, dk, [], e.ctxt);
            return msg;
          } else {
            return Failure("bad dk");
          }
        case None =>
          return Failure("no dk?");
    }
  }
}
