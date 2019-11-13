include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"
include "../Util/UTF8.dfy"


module {:extern "Materials"} Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import AlgorithmSuite

  type EncryptionContext = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  function method GetKeysFromEncryptionContext(encryptionContext: EncryptionContext): set<UTF8.ValidUTF8Bytes> {
    set i | 0 <= i < |encryptionContext| :: encryptionContext[i].0
  }

  const EC_PUBLIC_KEY_FIELD := UTF8.Encode("aws-crypto-public-key").value
  ghost const ReservedKeyValues := { EC_PUBLIC_KEY_FIELD }

  datatype EncryptedDataKey = EncryptedDataKey(providerID : UTF8.ValidUTF8Bytes,
                                               providerInfo : seq<uint8>,
                                               ciphertext : seq<uint8>)
  {
    predicate Valid() {
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }

    static function method ValidWitness(): EncryptedDataKey {
      EncryptedDataKey([], [], [])
    }
  }

  type ValidEncryptedDataKey = i : EncryptedDataKey | i.Valid() witness EncryptedDataKey.ValidWitness()

  // TODO: Add keyring trace
  datatype DataKeyMaterials = DataKeyMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                               plaintextDataKey: seq<uint8>,
                                               encryptedDataKeys: seq<ValidEncryptedDataKey>) 
  {
    predicate method Valid() {
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
    }

    static function method ValidWitness(): DataKeyMaterials { 
      DataKeyMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, 
                      seq(32, i => 0), 
                      [EncryptedDataKey.ValidWitness()])
    }
  }

  type ValidDataKeyMaterials = i: DataKeyMaterials | i.Valid() witness DataKeyMaterials.ValidWitness()

  predicate method CompatibleDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials) {
    k1.algorithmSuiteID == k2.algorithmSuiteID && k1.plaintextDataKey == k2.plaintextDataKey
  }

  function method MergeDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials): (res: ValidDataKeyMaterials)
    requires CompatibleDataKeyMaterials(k1, k2)
    ensures res.algorithmSuiteID == k1.algorithmSuiteID == k2.algorithmSuiteID
    ensures res.plaintextDataKey == k1.plaintextDataKey == k2.plaintextDataKey
    ensures res.encryptedDataKeys == k1.encryptedDataKeys + k2.encryptedDataKeys
  {
    var r := DataKeyMaterials(k1.algorithmSuiteID, k1.plaintextDataKey, k1.encryptedDataKeys + k2.encryptedDataKeys);
    r
  }

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext,
                                                     dataKeyMaterials: ValidDataKeyMaterials,
                                                     signingKey: Option<seq<uint8>>)
  {
    predicate method Valid() {
      && dataKeyMaterials.algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?
      && |dataKeyMaterials.encryptedDataKeys| > 0
    }

    static function method ValidWitness(): EncryptionMaterials { 
       EncryptionMaterials([], DataKeyMaterials.ValidWitness(), Some(seq(32, i => 0)))
    }
  }
  type ValidEncryptionMaterials = i: EncryptionMaterials | i.Valid() witness EncryptionMaterials.ValidWitness()

  // TODO: Add keyring trace
  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                                     encryptionContext: EncryptionContext,
                                                     plaintextDataKey: seq<uint8>,
                                                     verificationKey: Option<seq<uint8>>)
  {
    predicate method Valid() {
      && algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      && algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?
    }

    static function method ValidWitness(): DecryptionMaterials { 
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                          [], seq(32, i => 0), Some(seq(32, i => 0)))
    }
  }
  type ValidDecryptionMaterials = i: DecryptionMaterials | i.Valid() witness DecryptionMaterials.ValidWitness()

    //TODO: Review this code.
    function method naive_merge<T> (x : seq<T>, y : seq<T>, lt : (T, T) -> bool) : seq<T>
    {
        if |x| == 0 then y
        else if |y| == 0 then x
        else if lt(x[0], y[0]) then [x[0]] + naive_merge(x[1..], y, lt)
        else [y[0]] + naive_merge(x, y[1..], lt)
    }

    function method naive_merge_sort<T> (x : seq<T>, lt : (T, T) -> bool) : seq<T>
    {
        if |x| < 2 then x else
        var t := |x| / 2; naive_merge(naive_merge_sort(x[..t], lt), naive_merge_sort(x[t..], lt), lt)

    }

    function method memcmp_le (a : seq<uint8>, b : seq<uint8>, len : nat) : (res : Option<bool>)
        requires |a| >= len
        requires |b| >= len {
        if len == 0 then None else if a[0] != b[0] then Some(a[0] < b[0]) else memcmp_le (a[1..], b[1..], len - 1)
    }

    predicate method lex_lt(b : seq<uint8>, a : seq<uint8>)
    {
        match memcmp_le(a,b, if |a| < |b| then |a| else |b|) {
        case Some(b) => !b
        case None => !(|a| <= |b|)
        }
    }

    predicate method lt_keys(b : (seq<uint8>, seq<uint8>), a : (seq<uint8>, seq<uint8>)) {
        lex_lt(b.0, a.0)
    }

    function method EncCtxFlatten (x : seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): UTF8.ValidUTF8Bytes {
        if x == [] then [] else
        x[0].0 + x[0].1 + EncCtxFlatten(x[1..])
    }

    function method FlattenSortEncCtx(x : seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): UTF8.ValidUTF8Bytes
    {
        EncCtxFlatten(naive_merge_sort(x, lt_keys))
    }

    function method EncCtxLookup(x : seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>, k : UTF8.ValidUTF8Bytes): Option<UTF8.ValidUTF8Bytes>
    {
        if |x| == 0 then None else
        if x[0].0 == k then Some(x[0].1) else EncCtxLookup(x[1..], k)
    }

    function method EncCtxOfStrings(x : seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>  {
        if x == [] then [] else
        [(x[0].0, x[0].1)] + EncCtxOfStrings(x[1..])
    }
}
