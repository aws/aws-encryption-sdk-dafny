include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"
include "Defs.dfy"
include "../AlgorithmSuite.dfy"
include "../Materials.dfy"
include "../../Crypto/Signature.dfy"
include "../../Util/Streams.dfy"
include "../Serialize.dfy"
include "../MessageHeader.dfy"
include "../../Util/Time.dfy"

module CachingCMMDef {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import AlgorithmSuite
  import Materials
  import Signature
  import Streams
  import Serialize
  import MessageHeader
  import Time

  // The specification says:
  //  -- the default bytes limit must not exceed 2^63 - 1
  //  -- the default message limit is 2^32
  //  -- nothing about the default time-to-live limit
  const DEFAULT_TIME_TO_LIVE_LIMIT: nat := 3600  // in seconds
  const DEFAULT_BYTE_USE_LIMIT: uint64 := 0x7FFF_FFFF_FFFF_FFFF  // 2^63 - 1
  const DEFAULT_MESSAGE_USE_LIMIT: uint64 := 0x1_0000_0000  // 2^32

  const CACHE_ID_HASH_ALGORITHM := Signature.ECDSAParams.ECDSA_P384  // note, ESDK Java uses "SHA-512"

  /* Notes:
   *
   * For GetEncryptionMaterials, the specification talks about
   *     "If a cache entry is found" and
   *     "If a cache entry is not found"
   * and says nothing about expiry. For DecryptMaterials, the corresponding specification says
   *     "If a cache entry is found" and
   *     "If a cache entry is not found or the cache entry is expired".
   * The code below considers expiry in all cases. It also considers the indicated bytes and
   * message-count limits.
   *
   * The specification says a Caching CMM MUST have a partition ID, which avoids collisions
   * when several Caching CMMs share one CMC. This implementation never shares a CMC, so the
   * partition ID is omitted.
   *
   * The Java implementation bypasses the cache in several reasonable ways that are not mentioned
   * in the specification:
   *  - Bypass cache when performing streaming operations, unless the stream size is set before
   *    writing any data.
   *  - Bypass cache when "plaintextLen" is not specified.
   * The implementation below also bypasses the cache when "plaintextLen" is not specified.
   */

  class CachingCMM extends CMMDefs.CMM {
    const cmm: CMMDefs.CMM
    const cmc: CryptographicMaterialsCache
    const timeToLiveLimit: nat  // in seconds
    const bytesLimit: uint64
    const messagesLimit: uint64

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      cmm in Repr && cmm.Repr <= Repr && this !in cmm.Repr && cmm.Valid() &&
      cmc in Repr && cmc.Repr <= Repr && this !in cmc.Repr && cmc.Valid() &&
      cmm.Repr !! cmc.Repr
    }

    constructor (cmm: CMMDefs.CMM)
      requires cmm.Valid()
      ensures Valid() && fresh(Repr - old(cmm.Repr))
      ensures this.cmm == cmm
    {
      this.timeToLiveLimit := DEFAULT_TIME_TO_LIVE_LIMIT;
      this.bytesLimit := DEFAULT_BYTE_USE_LIMIT;
      this.messagesLimit := DEFAULT_MESSAGE_USE_LIMIT;

      this.cmm := cmm;
      var cmc := new CryptographicMaterialsCache();
      assert cmc in cmc.Repr;
      this.cmc := cmc;
      Repr := {this} + cmm.Repr + cmc.Repr;
    }

    method GetEncryptionMaterials(materialsRequest: Materials.EncryptionMaterialsRequest)
                                  returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(materialsRequest.encryptionContext)
      requires materialsRequest.encryptionContext.Keys !! Materials.ReservedKeyValues
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? ==> |res.value.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==>
        match res.value.algorithmSuiteID.SignatureType()
          case None => true
          case Some(sigType) =>
            res.value.signingKey.Some?
    {
      if materialsRequest.plaintextLength.None?
      || bytesLimit as int <= materialsRequest.plaintextLength.get
      || (materialsRequest.algorithmSuiteID.Some? && materialsRequest.algorithmSuiteID.get.ContainsIdentityKDF())
      {
        // So, get encryption materials from the underlying CMM.
        res := cmm.GetEncryptionMaterials(materialsRequest);
        Repr := Repr + cmm.Repr;
        return;
      }

      var cacheID :- ComputeCacheID(materialsRequest.algorithmSuiteID, materialsRequest.encryptionContext);

      var entry := cmc.LookupEncrypt(cacheID);
      Repr := Repr + cmc.Repr;
      if entry != null {
        entry.IncrementUse(materialsRequest.plaintextLength.get, 1);
        var currentTime := Time.GetCurrent();
        if entry.expiryTime <= currentTime
        || bytesLimit as nat <= entry.bytesEncrypted
        || messagesLimit as nat <= entry.messagesEncrypted
        {
          // Note, the specification says to treat these numbers as uint64, but the Java ESDK
          // treats them as signed int64.
          cmc.EvictEncrypt(cacheID);
          Repr := Repr + cmc.Repr;
        } else {
          return Success(entry.encMat);
        }
      }

      // Get encryption materials from the underlying CMM, but use None for the plaintext
      // length (since the caching returns encryption materials that are independent of
      // plaintext length).
      res := cmm.GetEncryptionMaterials(materialsRequest.(plaintextLength := None));
      Repr := Repr + cmm.Repr;
      var encMat :- res;
      // Add them to the cache.
      entry := cmc.AddEncrypt(cacheID, encMat, DEFAULT_TIME_TO_LIVE_LIMIT);
      Repr := Repr + cmc.Repr;
      entry.IncrementUse(materialsRequest.plaintextLength.get, 1);
      return Success(encMat);
    }

    method DecryptMaterials(materialsRequest: Materials.ValidDecryptionMaterialsRequest)
                            returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures res.Success? ==> res.value.plaintextDataKey.Some? && res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey.get)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
    {
      var cacheID :- ComputeCacheID(Some(materialsRequest.algorithmSuiteID), materialsRequest.encryptionContext);

      var entry := cmc.LookupDecrypt(cacheID);
      Repr := Repr + cmc.Repr;
      if entry != null {
        var currentTime := Time.GetCurrent();
        if entry.expiryTime <= currentTime {
          cmc.EvictDecrypt(cacheID);
          Repr := Repr + cmc.Repr;
        } else {
          return Success(entry.decMat);
        }
      }

      // Get decryption materials from the underlying CMM.
      res := cmm.DecryptMaterials(materialsRequest);
      Repr := Repr + cmm.Repr;
      var decMat :- res;
      // Add them to the cache.
      entry := cmc.AddDecrypt(cacheID, decMat, DEFAULT_TIME_TO_LIVE_LIMIT);
      Repr := Repr + cmc.Repr;
      return Success(decMat);
    }
  }


  method ComputeCacheID(algSuiteID: Option<AlgorithmSuite.ID>, encCtx: Materials.EncryptionContext) returns (res: Result<seq<uint8>>)
    requires MessageHeader.ValidAAD(encCtx)
  {
    var wr := new Streams.ByteWriter();

    // Note, if a partition ID were used, write the partition ID hash to wr here

    match algSuiteID {
      case None =>
        var _ := wr.WriteByte(0);
      case Some(algID) =>
        var _ := wr.WriteByte(1);
        var _ := wr.WriteUInt16(algID as uint16);
    }

    var encCtxWr := new Streams.ByteWriter();
    var _ :- Serialize.SerializeAAD(encCtxWr, encCtx);
    var encCtxEncoding :- Signature.Digest(CACHE_ID_HASH_ALGORITHM, encCtxWr.GetDataWritten());
    var _ := wr.WriteBytes(encCtxEncoding);

    res := Signature.Digest(CACHE_ID_HASH_ALGORITHM, wr.GetDataWritten());
  }

  predicate GoodEncMat(encMat: Materials.EncryptionMaterials) {
    |encMat.encryptedDataKeys| > 0 &&
    MessageHeader.ValidAAD(encMat.encryptionContext) &&
    match encMat.algorithmSuiteID.SignatureType()
      case None => true
      case Some(sigType) =>
        encMat.signingKey.Some?
  }

  predicate GoodDecMat(decMat: Materials.DecryptionMaterials) {
    decMat.plaintextDataKey.Some? && |decMat.plaintextDataKey.get| == decMat.algorithmSuiteID.KeyLength() &&
    (decMat.algorithmSuiteID.SignatureType().Some? ==> decMat.verificationKey.Some?)
  }

  class CryptographicMaterialsCache {
    ghost var Repr: set<object>
    var EM: map<seq<uint8>, CacheEntryEncrypt>
    var DM: map<seq<uint8>, CacheEntryDecrypt>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      (forall id :: id in EM.Keys ==> EM[id] in Repr && GoodEncMat(EM[id].encMat)) &&
      (forall id :: id in DM.Keys ==> DM[id] in Repr && GoodDecMat(DM[id].decMat))
    }

    constructor ()
      ensures Valid() && fresh(Repr)
    {
      Repr, EM, DM := {this}, map[], map[];
    }

    function method LookupEncrypt(cacheID: seq<uint8>): (entry: CacheEntryEncrypt?)
      requires Valid()
      reads Repr
      ensures entry != null ==> entry in Repr && GoodEncMat(entry.encMat)
    {
      if cacheID in EM.Keys then EM[cacheID] else null
    }

    function method LookupDecrypt(cacheID: seq<uint8>): (entry: CacheEntryDecrypt?)
      requires Valid()
      reads Repr
      ensures entry != null ==> entry in Repr && GoodDecMat(entry.decMat)
    {
      if cacheID in DM.Keys then DM[cacheID] else null
    }

    // Adds an entry [cacheID := encMat] to the cache, replacing any previous encrypt entry for cacheID
    // and initializing usage limits to (currentTime + timeToLiveLimit, 0, 0). Returns the resulting entry.
    method AddEncrypt(cacheID: seq<uint8>, encMat: Materials.ValidEncryptionMaterials, timeToLiveLimit: nat) returns (entry: CacheEntryEncrypt)
      requires Valid() && GoodEncMat(encMat) && 0 < timeToLiveLimit
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr)) && entry in Repr
    {
      entry := new CacheEntryEncrypt(encMat, timeToLiveLimit);
      Repr := Repr + {entry};
      EM := EM[cacheID := entry];
    }

    // Adds an entry [cacheID := decMat] to the cache, replacing any previous decrypt entry for cacheID
    // and initializing usage limits to (currentTime + timeToLiveLimit). Returns the resulting entry.
    method AddDecrypt(cacheID: seq<uint8>, decMat: Materials.ValidDecryptionMaterials, timeToLiveLimit: nat) returns (entry: CacheEntryDecrypt)
      requires Valid() && GoodDecMat(decMat) && 0 < timeToLiveLimit
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr)) && entry in Repr
    {
      entry := new CacheEntryDecrypt(decMat, timeToLiveLimit);
      Repr := Repr + {entry};
      DM := DM[cacheID := entry];
    }

    // Removes any encrypt entry for cacheID.
    method EvictEncrypt(cacheID: seq<uint8>)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
    {
      EM := map id | id in EM.Keys && id != cacheID :: EM[id];
    }

    // Removes any decrypt entry for cacheID.
    method EvictDecrypt(cacheID: seq<uint8>)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
    {
      DM := map id | id in DM.Keys && id != cacheID :: DM[id];
    }
  }

  class CacheEntryEncrypt {
    const encMat: Materials.ValidEncryptionMaterials
    const expiryTime: nat
    var messagesEncrypted: nat
    var bytesEncrypted: nat

    constructor (encMat: Materials.ValidEncryptionMaterials, timeToLiveLimit: nat)
      ensures messagesEncrypted == bytesEncrypted == 0
      ensures this.encMat == encMat
    {
      this.encMat := encMat;
      var currentTime := Time.GetCurrent();
      expiryTime := currentTime + timeToLiveLimit;
      messagesEncrypted, bytesEncrypted := 0, 0;
    }

    method IncrementUse(byteCount: nat, useCount: nat)
      modifies this
      ensures messagesEncrypted == old(messagesEncrypted) + byteCount
      ensures bytesEncrypted == old(bytesEncrypted) + useCount
    {
      messagesEncrypted := messagesEncrypted + byteCount;
      bytesEncrypted := bytesEncrypted + useCount;
    }
  }


  class CacheEntryDecrypt {
    const decMat: Materials.ValidDecryptionMaterials
    const expiryTime: nat

    constructor (decMat: Materials.ValidDecryptionMaterials, timeToLiveLimit: nat)
      ensures this.decMat == decMat
    {
      this.decMat := decMat;
      var currentTime := Time.GetCurrent();
      expiryTime := currentTime + timeToLiveLimit;
    }
  }
}
