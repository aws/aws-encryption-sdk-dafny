include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"
include "../Util/UTF8.dfy"

module {:extern "Materials"} Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import AlgorithmSuite

  // TODO: Update EncryptionContext structure to a map structure.
  // https://github.com/awslabs/aws-encryption-sdk-dafny/issues/50
  type EncryptionContext = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  function method GetKeysFromEncryptionContext(encryptionContext: EncryptionContext): set<UTF8.ValidUTF8Bytes> {
    set i | 0 <= i < |encryptionContext| :: encryptionContext[i].0
  }

  method EncryptionContextGet(encryptionContext: EncryptionContext, key: UTF8.ValidUTF8Bytes) returns (res: Result<UTF8.ValidUTF8Bytes>)
    ensures match EncCtxLookup(encryptionContext, key)
            case Some(value) => res.Success? && res.value == value
            case None => res.Failure? && res.error == "Key not found."
  {
    res := Failure("Key not found.");
    var i := 0;
    while i < |encryptionContext|
      invariant i <= |encryptionContext|
      invariant forall j :: 0 <= j < i ==> encryptionContext[j].0 != key
    {
      if encryptionContext[i].0 == key {
        res := Success(encryptionContext[i].1);
        return res;
      }
      i := i + 1;
    }
  }

  function EncCtxLookup(x: EncryptionContext, k: UTF8.ValidUTF8Bytes): Option<UTF8.ValidUTF8Bytes>
  {
    match EncCtxIndexLookup(x, k)
    case Some(i) => Some(x[i].1)
    case None => None
  }

  function EncCtxIndexLookup(x: EncryptionContext, k: UTF8.ValidUTF8Bytes): (opt: Option<nat>)
  {
    FunctionFind(x, (y: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)) => y.0 == k, 0)
  }

  const EC_PUBLIC_KEY_FIELD := UTF8.Encode("aws-crypto-public-key").value
  ghost const ReservedKeyValues := { EC_PUBLIC_KEY_FIELD }

  datatype EncryptedDataKey = EncryptedDataKey(providerID: UTF8.ValidUTF8Bytes,
                                               providerInfo: seq<uint8>,
                                               ciphertext: seq<uint8>)
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

  datatype KeyringTraceFlag =
  | GENERATED_DATA_KEY
  | ENCRYPTED_DATA_KEY
  | DECRYPTED_DATA_KEY
  | SIGNED_ENCRYPTION_CONTEXT
  | VERIFIED_ENCRYPTION_CONTEXT

  datatype KeyringTraceEntry = KeyringTraceEntry(keyNamespace: UTF8.ValidUTF8Bytes,
                                                 keyName: UTF8.ValidUTF8Bytes,
                                                 flags: set<KeyringTraceFlag>)

  predicate method IsGenerateTraceEntry(entry: KeyringTraceEntry) {
    GENERATED_DATA_KEY in entry.flags
  }

  predicate method IsEncryptTraceEntry(entry: KeyringTraceEntry) {
    ENCRYPTED_DATA_KEY in entry.flags
  }

  predicate method IsDecryptTraceEntry(entry: KeyringTraceEntry) {
    DECRYPTED_DATA_KEY in entry.flags
  }

  const ValidEncryptionMaterialFlags: set<KeyringTraceFlag> := {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY};
  const ValidDecryptionMaterialFlags: set<KeyringTraceFlag> := {DECRYPTED_DATA_KEY, VERIFIED_ENCRYPTION_CONTEXT};

  datatype DataKeyMaterials = DataKeyMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                               plaintextDataKey: seq<uint8>,
                                               encryptedDataKeys: seq<ValidEncryptedDataKey>,
                                               keyringTrace: seq<KeyringTraceEntry>)
  {
    predicate Valid() {
      var generateTraces := Filter(keyringTrace, IsGenerateTraceEntry);
      var encryptTraces := Filter(keyringTrace, IsEncryptTraceEntry);
      && algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      && (forall entry :: entry in keyringTrace ==> entry.flags <= ValidEncryptionMaterialFlags)
      && (forall entry :: entry in keyringTrace ==> IsGenerateTraceEntry(entry) || IsEncryptTraceEntry(entry))
      && |generateTraces| <= 1
      && (|generateTraces| == 1 ==> keyringTrace[0] == generateTraces[0])
      && |encryptTraces| == |encryptedDataKeys|
      // TODO: Strongly tie each trace entry to it's corresponding EDK (https://github.com/awslabs/aws-encryption-sdk-dafny/issues/100)
    }

    static function method ValidWitness(): DataKeyMaterials {
      DataKeyMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                      seq(32, i => 0),
                      [EncryptedDataKey.ValidWitness()],
                      [KeyringTraceEntry([], [], {ENCRYPTED_DATA_KEY, GENERATED_DATA_KEY})])
    }
  }

  type ValidDataKeyMaterials = i: DataKeyMaterials | i.Valid() witness DataKeyMaterials.ValidWitness()

  predicate method CompatibleDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials) {
    var generateTraces := Filter(k1.keyringTrace + k2.keyringTrace, IsGenerateTraceEntry);
    k1.algorithmSuiteID == k2.algorithmSuiteID && k1.plaintextDataKey == k2.plaintextDataKey
    && |generateTraces| <= 1
    && (|generateTraces| == 1 ==> |k1.keyringTrace| > 0 && generateTraces[0] == k1.keyringTrace[0])
  }

  function method ConcatDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials): (res: ValidDataKeyMaterials)
    requires CompatibleDataKeyMaterials(k1, k2)
    ensures res.algorithmSuiteID == k1.algorithmSuiteID == k2.algorithmSuiteID
    ensures res.plaintextDataKey == k1.plaintextDataKey == k2.plaintextDataKey
    ensures res.encryptedDataKeys == k1.encryptedDataKeys + k2.encryptedDataKeys
    ensures res.keyringTrace == k1.keyringTrace + k2.keyringTrace
  {
    FilterIsDistributive(k1.keyringTrace, k2.keyringTrace, IsEncryptTraceEntry);
    FilterIsDistributive(k1.keyringTrace, k2.keyringTrace, IsGenerateTraceEntry);
    var r := DataKeyMaterials(k1.algorithmSuiteID, k1.plaintextDataKey, k1.encryptedDataKeys + k2.encryptedDataKeys, k1.keyringTrace + k2.keyringTrace);
    r
  }

  datatype OnDecryptResult = OnDecryptResult(algorithmSuiteID: AlgorithmSuite.ID,
                                             plaintextDataKey: seq<uint8>,
                                             keyringTrace: seq<KeyringTraceEntry>)
  {
    predicate Valid() {
      && algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      && (forall entry :: entry in keyringTrace ==> entry.flags <= ValidDecryptionMaterialFlags)
    }

    static function method ValidWitness(): OnDecryptResult {
      var pdk := seq(32, i => 0);
      var entry := KeyringTraceEntry([], [], {DECRYPTED_DATA_KEY});
      var r := OnDecryptResult(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                      pdk, [entry]);
      r
    }
  }

  type ValidOnDecryptResult = i: OnDecryptResult | i.Valid() witness OnDecryptResult.ValidWitness()

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext,
                                                     dataKeyMaterials: ValidDataKeyMaterials,
                                                     signingKey: Option<seq<uint8>>)
  {
    predicate Valid() {
      && dataKeyMaterials.algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?
      && |dataKeyMaterials.encryptedDataKeys| > 0
    }

    static function method ValidWitness(): EncryptionMaterials {
      EncryptionMaterials([], DataKeyMaterials.ValidWitness(), Some(seq(32, i => 0)))
    }
  }

  type ValidEncryptionMaterials = i: EncryptionMaterials | i.Valid() witness EncryptionMaterials.ValidWitness()

  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                                     encryptionContext: EncryptionContext,
                                                     plaintextDataKey: seq<uint8>,
                                                     verificationKey: Option<seq<uint8>>,
                                                     keyringTrace: seq<KeyringTraceEntry>)

  {
    predicate Valid() {
      && algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      && algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?
      && (forall entry :: entry in keyringTrace ==> entry.flags <= ValidDecryptionMaterialFlags)
    }

    static function method ValidWitness(): DecryptionMaterials {
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                          [], seq(32, i => 0), Some(seq(32, i => 0)),
                          [KeyringTraceEntry([], [], {DECRYPTED_DATA_KEY})])
    }
  }

  type ValidDecryptionMaterials = i: DecryptionMaterials | i.Valid() witness DecryptionMaterials.ValidWitness()
}
