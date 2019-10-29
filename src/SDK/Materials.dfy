include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"


module Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite

  // TODO-RS: Are these intended to be UTF8?
  type EncryptionContext = seq<(seq<uint8>, seq<uint8>)>

  function method GetKeysFromEncryptionContext(encryptionContext: EncryptionContext): set<seq<uint8>> {
    set i | 0 <= i < |encryptionContext| :: encryptionContext[i].0
  }

  const EC_PUBLIC_KEY_FIELD: seq<uint8> := StringToByteSeq("aws-crypto-public-key");
  ghost const ReservedKeyValues := { EC_PUBLIC_KEY_FIELD }

  datatype EncryptedDataKey = EncryptedDataKey(providerID : string,
                                               providerInfo : seq<uint8>,
                                               ciphertext : seq<uint8>)
  {
    predicate Valid() {
      StringIs8Bit(providerID) &&
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }
  }

  // TODO: Add keyring trace
  datatype EncryptionMaterialsInput = EncryptionMaterialsInput(algorithmSuiteID: AlgorithmSuite.ID,
                                                               encryptionContext: EncryptionContext,
                                                               plaintextDataKey: Option<seq<uint8>>) 
  {
    predicate Valid() {
      (plaintextDataKey.None? || algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get))
    }
  }
  type ValidEncryptionMaterialsInput = i: EncryptionMaterialsInput | i.Valid() witness EncryptionMaterialsInput(0x0014, [], None)

  datatype DataKey = DataKey(algorithmSuiteID: AlgorithmSuite.ID, // TODO-RS: This could be a ghost var?
                             plaintextDataKey: seq<uint8>,
                             encryptedDataKeys: seq<EncryptedDataKey>) 
  {
    predicate method Valid() {
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      // TODO-RS: assert that the encrypted data keys are actually tied to the plaintext!
    }
  }

  function method ValidDataKeyWitness(): DataKey { 
    DataKey(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, seq(32, i => 0), [])
  }  
  type ValidDataKey = i: DataKey | i.Valid() witness ValidDataKeyWitness()

  predicate method CompatibleDataKeys(k1: ValidDataKey, k2: ValidDataKey) {
    k1.algorithmSuiteID == k2.algorithmSuiteID && k1.plaintextDataKey == k2.plaintextDataKey
  }

  function method MergeDataKeys(k1: ValidDataKey, k2: ValidDataKey): (res: ValidDataKey)
    requires CompatibleDataKeys(k1, k2)
    ensures res.algorithmSuiteID == k1.algorithmSuiteID == k2.algorithmSuiteID
    ensures res.plaintextDataKey == k1.plaintextDataKey == k2.plaintextDataKey
    ensures res.encryptedDataKeys == k1.encryptedDataKeys + k2.encryptedDataKeys
  {
    var r := DataKey(k1.algorithmSuiteID, k1.plaintextDataKey, k1.encryptedDataKeys + k2.encryptedDataKeys);
    r
  }

  predicate method ValidOnEncryptResult(input: ValidEncryptionMaterialsInput, output: ValidDataKey) {
    input.algorithmSuiteID == output.algorithmSuiteID &&
    input.plaintextDataKey.Some? ==> input.plaintextDataKey.get == output.plaintextDataKey
  }

  lemma ValidOnEncryptResultImpliesSameAlgorithmSuiteID(input: ValidEncryptionMaterialsInput, output: ValidDataKey) 
    requires ValidOnEncryptResult(input, output)
    ensures input.algorithmSuiteID == output.algorithmSuiteID
  
  lemma MergingResults(input: ValidEncryptionMaterialsInput, dk1: ValidDataKey, dk2: ValidDataKey) 
    requires ValidOnEncryptResult(input, dk1)
    requires ValidOnEncryptResult(input, dk2)
    requires dk1.plaintextDataKey == dk2.plaintextDataKey
    ensures CompatibleDataKeys(dk1, dk2)
    ensures ValidOnEncryptResult(input, MergeDataKeys(dk1, dk2)) 
  {
    ValidOnEncryptResultImpliesSameAlgorithmSuiteID(input, dk1);
    ValidOnEncryptResultImpliesSameAlgorithmSuiteID(input, dk2);
    assert input.algorithmSuiteID == dk1.algorithmSuiteID == dk2.algorithmSuiteID;
    if (input.plaintextDataKey.Some?) {
      assert input.plaintextDataKey.get == dk1.plaintextDataKey == dk2.plaintextDataKey;
    }
  }

  datatype EncryptionMaterialsOutput = EncryptionMaterialsOutput(dataKey: ValidDataKey,
                                                                 signingKey: Option<seq<uint8>>)
  {
    predicate method Valid() {
      dataKey.algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?
    }
  }
  type ValidEncryptionMaterialsOutput = i: EncryptionMaterialsOutput | i.Valid() 
    witness EncryptionMaterialsOutput(ValidDataKeyWitness(), Some(seq(32, i => 0)))

  // TODO: Add keyring trace
  datatype DecryptionMaterialsOutput = DecryptionMaterialsOutput(dataKey: ValidDataKey,
                                                                 verificationKey: Option<seq<uint8>>)
      dataKey.algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?
    }
  }
  type ValidDecryptionMaterialsOutput = i: DecryptionMaterialsOutput | i.Valid() 
    witness DecryptionMaterialsOutput(ValidDataKeyWitness(), Some(seq(32, i => 0)))

  predicate method ValidOnDecryptResult(algorithmSuiteID: AlgorithmSuite.ID, 
                                        encryptionContext: EncryptionContext, 
                                        edks: seq<EncryptedDataKey>, 
                                        output: ValidDataKey) {
    output.algorithmSuiteID == algorithmSuiteID &&
    output.encryptedDataKeys == edks
  }

  lemma ValidOnDecryptResultImpliesSameAlgorithmSuiteID(algorithmSuiteID: AlgorithmSuite.ID, 
                                                        encryptionContext: EncryptionContext, 
                                                        edks: seq<EncryptedDataKey>, 
                                                        output: ValidDataKey)
    requires ValidOnDecryptResult(algorithmSuiteID, encryptionContext, edks, output)
    ensures output.algorithmSuiteID == algorithmSuiteID
  {}

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

    function method EncCtxFlatten (x : seq<(seq<uint8>, seq<uint8>)>) : seq<uint8> {
        if x == [] then [] else
        x[0].0 + x[0].1 + EncCtxFlatten(x[1..])
    }

    function method FlattenSortEncCtx(x : seq<(seq<uint8>, seq<uint8>)>) : seq<uint8>
    {
        EncCtxFlatten(naive_merge_sort(x, lt_keys))
    }

    function method enc_ctx_lookup(x : seq<(seq<uint8>, seq<uint8>)>, k : seq<uint8>) : Option<seq<uint8>>
    {
        if |x| == 0 then None else
        if x[0].0 == k then Some(x[0].1) else enc_ctx_lookup(x[1..], k)
    }

    function method enc_ctx_of_strings(x : seq<(string, string)>) : seq<(seq<uint8>, seq<uint8>)>  {
        if x == [] then [] else
        [(StringToByteSeqLossy(x[0].0), StringToByteSeqLossy(x[0].1))] + enc_ctx_of_strings(x[1..])
    }
}
