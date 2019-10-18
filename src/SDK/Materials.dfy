include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"

module Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite

  type EncryptionContext = seq<(seq<uint8>, seq<uint8>)>

  function method GetKeysFromEncryptionContext(encryptionContext: EncryptionContext): set<seq<uint8>> {
    set i | 0 <= i < |encryptionContext| :: encryptionContext[i].0
  }

  const EC_PUBLIC_KEY_FIELD: seq<uint8> := StringToByteSeq("aws-crypto-public-key");
  ghost const ReservedKeyValues := { EC_PUBLIC_KEY_FIELD }

  datatype EncryptedDataKey = EncryptedDataKey(providerID: string,
                                               providerInfo: seq<uint8>,
                                               ciphertext: seq<uint8>)
  {
    predicate Valid() {
      StringIs8Bit(providerID) &&
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }
  }

  datatype KeyringTraceFlag =
  | GENERATED_DATA_KEY
  | ENCRYPTED_DATA_KEY
  | DECRYPTED_DATA_KEY
  | SIGNED_ENCRYPTION_CONTEXT
  | VERIFIED_ENCRYPTION_CONTEXT

  datatype KeyringTraceEntry = KeyringTraceEntry(keyNamespace: string,
                                                 keyName: string,
                                                 flags: set<KeyringTraceFlag>)

  type KeyringTrace = seq<KeyringTraceEntry>

  // TODO is there a better location for these predicates?
  predicate TraceHasGenerateFlag(trace: KeyringTraceEntry) {
    GENERATED_DATA_KEY in trace.flags
  }

  predicate TraceHasEncryptFlag(trace: KeyringTraceEntry) {
    ENCRYPTED_DATA_KEY in trace.flags
  }
    
  predicate TraceHasDecryptFlag(trace: KeyringTraceEntry) {
    DECRYPTED_DATA_KEY in trace.flags
  }

  const WrappingFlags: set<KeyringTraceFlag> := {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT};
  const UnwrappingFlags: set<KeyringTraceFlag> := {DECRYPTED_DATA_KEY, VERIFIED_ENCRYPTION_CONTEXT};

  // TODO: where does this belong?
  // Ghost predicate that describes a promise that the EDK
  // is the encrypted form of the plaintextDataKey.
  // This ensures that a set of EncryptionMaterials are invalid if, for example, the
  // plaintextDataKey is changed after an edk has ben previously set.
  predicate EDKMatchesPlaintextDataKey(edk: EncryptedDataKey, dataKey: Option<seq<uint8>>)
  {
    true
  }

  // TODO: where does this belong?
  // Ghost predicate that describes a promise that the EDK
  // corresponds with the trace.
  // This ensures that a set of EncryptionMaterials are invalid if, for example, the
  // keyringTrace is reordered or updated without this promise.
  predicate EDKMatchesKeyringTraceEntry(edk: EncryptedDataKey, trace: KeyringTraceEntry) {
    true
  }

  class EncryptionMaterials {
    var algorithmSuiteID: AlgorithmSuite.ID
    var encryptedDataKeys: seq<EncryptedDataKey>
    var encryptionContext: EncryptionContext
    var plaintextDataKey: Option<seq<uint8>>
    var signingKey: Option<seq<uint8>>
    var keyringTrace: KeyringTrace

    predicate Valid()
      reads this
    {
      var generateTraces := Filter(keyringTrace, TraceHasGenerateFlag);
      var encryptTraces := Filter(keyringTrace, TraceHasEncryptFlag);
      (plaintextDataKey.None? || |plaintextDataKey.get| == algorithmSuiteID.KeyLength()) &&
      (plaintextDataKey.None? ==> |encryptedDataKeys| == 0) &&
      (|encryptedDataKeys| > 0 ==> plaintextDataKey.Some?) &&
      (forall edk :: edk in encryptedDataKeys ==> EDKMatchesPlaintextDataKey(edk, plaintextDataKey)) &&
      (forall trace :: trace in keyringTrace ==> trace.flags <= WrappingFlags + {GENERATED_DATA_KEY}) &&
      (forall trace :: trace in keyringTrace ==> trace in generateTraces || trace in encryptTraces) &&
      (plaintextDataKey.Some? <==> |generateTraces| == 1) &&
      (plaintextDataKey.None? <==> |generateTraces| == 0) &&
      (|encryptedDataKeys| == |encryptTraces|) &&
      (forall i :: 0 <= i < |encryptedDataKeys| ==> EDKMatchesKeyringTraceEntry(encryptedDataKeys[i], encryptTraces[i]))
    }

    constructor(algorithmSuiteID: AlgorithmSuite.ID,
                encryptedDataKeys: seq<EncryptedDataKey>,
                encryptionContext: EncryptionContext,
                plaintextDataKey: Option<seq<uint8>>,
                signingKey: Option<seq<uint8>>,
                keyringTrace: seq<KeyringTraceEntry>)
      requires plaintextDataKey.None? || |plaintextDataKey.get| == algorithmSuiteID.KeyLength()
      requires plaintextDataKey.None? <==> |encryptedDataKeys| == 0
      requires |encryptedDataKeys| > 0 ==> plaintextDataKey.Some?
      requires forall edk :: edk in encryptedDataKeys ==> EDKMatchesPlaintextDataKey(edk, plaintextDataKey)
      requires forall trace :: trace in keyringTrace ==> trace.flags <= WrappingFlags + {GENERATED_DATA_KEY}
      requires forall trace :: trace in keyringTrace ==> 
        trace in Filter(keyringTrace, TraceHasGenerateFlag) ||
        trace in Filter(keyringTrace, TraceHasEncryptFlag)
      requires plaintextDataKey.Some? <==> |Filter(keyringTrace, TraceHasGenerateFlag)| == 1
      requires plaintextDataKey.None? <==> |Filter(keyringTrace, TraceHasGenerateFlag)| == 0
      requires |encryptedDataKeys| == |Filter(keyringTrace, TraceHasEncryptFlag)|
      requires forall i :: 0 <= i < |encryptedDataKeys| ==>
        encryptedDataKeys[i].providerID == Filter(keyringTrace, TraceHasEncryptFlag)[i].keyNamespace
      requires forall i :: 0 <= i < |encryptedDataKeys| ==>
        EDKMatchesKeyringTraceEntry(encryptedDataKeys[i], Filter(keyringTrace, TraceHasEncryptFlag)[i])
      ensures Valid()
      ensures this.algorithmSuiteID == algorithmSuiteID
      ensures this.encryptedDataKeys == encryptedDataKeys
      ensures this.encryptionContext == encryptionContext
      ensures this.plaintextDataKey == plaintextDataKey
      ensures this.keyringTrace == keyringTrace
    {
      this.algorithmSuiteID := algorithmSuiteID;
      this.encryptedDataKeys := encryptedDataKeys;
      this.encryptionContext := encryptionContext;
      this.plaintextDataKey := plaintextDataKey;
      this.signingKey := signingKey;
      this.keyringTrace := keyringTrace;
    }

    method SetPlaintextDataKey(dataKey: seq<uint8>, trace: KeyringTraceEntry)
      requires Valid()
      requires plaintextDataKey.None?
      requires trace.flags == {GENERATED_DATA_KEY}
      requires |dataKey| == algorithmSuiteID.KeyLength()
      modifies `plaintextDataKey, `keyringTrace
      ensures Valid()
      ensures plaintextDataKey == Some(dataKey)
      ensures keyringTrace == old(keyringTrace) + [trace]
    {
      FilterIsDistributive(keyringTrace, [trace], TraceHasEncryptFlag);
      FilterIsDistributive(keyringTrace, [trace], TraceHasGenerateFlag);
      plaintextDataKey := Some(dataKey);
      keyringTrace := keyringTrace + [trace];
    }

    method AppendEncryptedDataKey(edk: EncryptedDataKey, trace: KeyringTraceEntry)
      requires Valid()
      requires EDKMatchesPlaintextDataKey(edk, plaintextDataKey)
      requires plaintextDataKey.Some?
      requires ENCRYPTED_DATA_KEY in trace.flags
      requires trace.flags <= WrappingFlags
      requires trace.keyNamespace == edk.providerID
      requires EDKMatchesKeyringTraceEntry(edk, trace)
      modifies `encryptedDataKeys, `keyringTrace
      ensures Valid()
      ensures encryptedDataKeys == old(encryptedDataKeys) + [edk]
      ensures keyringTrace == old(keyringTrace) + [trace]
    {
      FilterIsDistributive(keyringTrace, [trace], TraceHasEncryptFlag);
      FilterIsDistributive(keyringTrace, [trace], TraceHasGenerateFlag);
      encryptedDataKeys := encryptedDataKeys + [edk]; // TODO: Determine if this is a performance issue
      keyringTrace := keyringTrace + [trace];
    }
  }

  class DecryptionMaterials {
    var algorithmSuiteID: AlgorithmSuite.ID
    var encryptionContext: EncryptionContext
    var plaintextDataKey: Option<seq<uint8>>
    var verificationKey: Option<seq<uint8>>
    var keyringTrace: KeyringTrace

    predicate Valid()
      reads this
    {
      var decryptTraces := Filter(keyringTrace, TraceHasDecryptFlag);
      (plaintextDataKey.None? || |plaintextDataKey.get| == algorithmSuiteID.KeyLength()) &&
      (forall trace :: trace in keyringTrace ==> trace.flags <= UnwrappingFlags) &&
      (forall trace :: trace in keyringTrace ==> trace in decryptTraces) &&
      (plaintextDataKey.Some? <==> |decryptTraces| == 1) &&
      (plaintextDataKey.None? <==> |decryptTraces| == 0)
    }

    constructor(algorithmSuiteID: AlgorithmSuite.ID,
                encryptionContext: EncryptionContext,
                plaintextDataKey: Option<seq<uint8>>,
                verificationKey: Option<seq<uint8>>,
                keyringTrace: seq<KeyringTraceEntry>)
      requires plaintextDataKey.None? || |plaintextDataKey.get| == algorithmSuiteID.KeyLength()
      requires forall trace :: trace in keyringTrace ==> trace.flags <= UnwrappingFlags
      requires forall trace :: trace in keyringTrace ==> trace in Filter(keyringTrace, TraceHasDecryptFlag)
      requires plaintextDataKey.Some? <==> |Filter(keyringTrace, TraceHasDecryptFlag)| == 1
      requires plaintextDataKey.None? <==> |Filter(keyringTrace, TraceHasDecryptFlag)| == 0
      ensures Valid()
      ensures this.algorithmSuiteID == algorithmSuiteID
      ensures this.encryptionContext == encryptionContext
      ensures this.plaintextDataKey == plaintextDataKey
      ensures this.verificationKey == verificationKey
      ensures this.keyringTrace == keyringTrace
    {
      this.algorithmSuiteID := algorithmSuiteID;
      this.encryptionContext := encryptionContext;
      this.plaintextDataKey := plaintextDataKey;
      this.verificationKey := verificationKey;
      this.keyringTrace := keyringTrace;
    }

    // TODO: Is there a way for us to ensure this within Valid()?
    // This method MUST be used to set the plaintextDataKey, as it ensures the
    // property that an EncryptionMaterial's plaintextDataKey can only be set once,
    // and keyringTrace is in order
    method SetPlaintextDataKey(dataKey: seq<uint8>, trace: KeyringTraceEntry)
      requires Valid()
      requires plaintextDataKey.None?
      requires trace.flags <= UnwrappingFlags
      requires DECRYPTED_DATA_KEY in trace.flags
      requires |dataKey| == algorithmSuiteID.KeyLength()
      modifies `plaintextDataKey, `keyringTrace
      ensures Valid()
      ensures plaintextDataKey == Some(dataKey)
      ensures keyringTrace == old(keyringTrace) + [trace]
    {
      FilterIsDistributive(keyringTrace, [trace], TraceHasDecryptFlag);
      plaintextDataKey := Some(dataKey);
      keyringTrace := keyringTrace + [trace];
    }

    method SetVerificationKey(verifKey: seq<uint8>)
      requires Valid()
      requires verificationKey.None?
      modifies `verificationKey
      ensures Valid()
      ensures verificationKey == Some(verifKey)
    {
      verificationKey := Some(verifKey);
    }
  }

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
