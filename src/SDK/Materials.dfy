include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"
include "../Util/UTF8.dfy"

module {:extern "Materials"} Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8
  import AlgorithmSuite


  type EncryptionContext = map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>

  // UTF-8 encoded "aws-crypto-public-key"
  const EC_PUBLIC_KEY_FIELD: UTF8.ValidUTF8Bytes :=
    [0x61, 0x77, 0x73, 0x2D, 0x63, 0x72, 0x79, 0x70, 0x74, 0x6F, 0x2D, 0x70,
    0x75, 0x62, 0x6C, 0x69, 0x63, 0x2D, 0x6B, 0x65, 0x79];
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

  predicate method IsEncryptionTraceEntry(entry: KeyringTraceEntry) {
    entry.flags <= ValidEncryptionMaterialFlags && (IsGenerateTraceEntry(entry) || IsEncryptTraceEntry(entry))
  }

  const ValidEncryptionMaterialFlags: set<KeyringTraceFlag> := {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY};
  const ValidDecryptionMaterialFlags: set<KeyringTraceFlag> := {DECRYPTED_DATA_KEY, VERIFIED_ENCRYPTION_CONTEXT};

  predicate GenerateTraceEntriesConsistent(plaintextDataKey: Option<seq<uint8>>, keyringTrace: seq<KeyringTraceEntry>) {
    var generateTraces := Filter(keyringTrace, IsGenerateTraceEntry);
    && |generateTraces| <= 1 
    && (|generateTraces| == 1 ==> plaintextDataKey.Some? && |keyringTrace| >= 1 && keyringTrace[0] == generateTraces[0])
    && (plaintextDataKey.None? ==> |keyringTrace| == 0)
  }

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext,
                                                     algorithmSuiteID: AlgorithmSuite.ID,
                                                     plaintextDataKey: Option<seq<uint8>>,
                                                     encryptedDataKeys: seq<ValidEncryptedDataKey>,
                                                     keyringTrace: seq<KeyringTraceEntry>,
                                                     signingKey: Option<seq<uint8>>)
  {
    predicate Valid() {
      && (algorithmSuiteID.SignatureType().Some? ==> signingKey.Some?)
      && (plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get))
      && GenerateTraceEntriesConsistent(plaintextDataKey, keyringTrace)
      && |Filter(keyringTrace, IsEncryptTraceEntry)| == |encryptedDataKeys|
      // TODO: Strongly tie each trace entry to it's corresponding EDK (https://github.com/awslabs/aws-encryption-sdk-dafny/issues/100)
    }

    static function method ValidWitness(): EncryptionMaterials {
      EncryptionMaterials(map[], 
                          AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                          None,
                          [],
                          [], 
                          Some(seq(32, i => 0)))
    }

    function method WithKeys(newPlaintextDataKey: Option<seq<uint8>>, 
                             newEncryptedDataKeys: seq<ValidEncryptedDataKey>,
                             newTraceEntries: seq<KeyringTraceEntry>): (res: ValidEncryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.Some? ==> newPlaintextDataKey == this.plaintextDataKey
      requires newPlaintextDataKey.Some? ==> this.algorithmSuiteID.ValidPlaintextDataKey(newPlaintextDataKey.get)
      requires (forall entry :: entry in newTraceEntries ==> IsEncryptionTraceEntry(entry))
      requires GenerateTraceEntriesConsistent(newPlaintextDataKey, keyringTrace + newTraceEntries)
      requires (newPlaintextDataKey != this.plaintextDataKey) <==> |Filter(newTraceEntries, IsGenerateTraceEntry)| == 1
      requires (newPlaintextDataKey == this.plaintextDataKey) ==> (forall entry :: entry in newTraceEntries ==> !IsGenerateTraceEntry(entry))
      requires |Filter(newTraceEntries, IsEncryptTraceEntry)| == |newEncryptedDataKeys|
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID 
      ensures newPlaintextDataKey == res.plaintextDataKey
      ensures this.keyringTrace + newTraceEntries == res.keyringTrace
      ensures this.encryptedDataKeys + newEncryptedDataKeys == res.encryptedDataKeys
      ensures this.signingKey == res.signingKey
    {
        var r := this.(plaintextDataKey := newPlaintextDataKey, 
                       encryptedDataKeys := encryptedDataKeys + newEncryptedDataKeys,
                       keyringTrace := keyringTrace + newTraceEntries);
        FilterIsDistributive(keyringTrace, newTraceEntries, IsEncryptTraceEntry);
        FilterIsDistributive(keyringTrace, newTraceEntries, IsGenerateTraceEntry);
        assert r.Valid();
        r
    }
  }

  type ValidEncryptionMaterials = i: EncryptionMaterials | i.Valid() witness EncryptionMaterials.ValidWitness()

  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID,
                                                     encryptionContext: EncryptionContext,
                                                     plaintextDataKey: Option<seq<uint8>>,
                                                     verificationKey: Option<seq<uint8>>,
                                                     keyringTrace: seq<KeyringTraceEntry>)
  {
    predicate Valid() {
      && (plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get))
      && (algorithmSuiteID.SignatureType().Some? ==> verificationKey.Some?)
      && (forall entry :: entry in keyringTrace ==> entry.flags <= ValidDecryptionMaterialFlags)
    }

    static function method ValidWitness(): DecryptionMaterials {
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
                          map[], Some(seq(32, i => 0)), Some(seq(32, i => 0)),
                          [KeyringTraceEntry([], [], {DECRYPTED_DATA_KEY})])
    }

    function method WithPlaintextDataKey(plaintextDataKey: seq<uint8>, newTraceEntries: seq<KeyringTraceEntry>): (res: ValidDecryptionMaterials)
      requires Valid()
      requires this.plaintextDataKey.None?
      requires algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey)
      requires forall entry :: entry in newTraceEntries ==> entry.flags <= ValidDecryptionMaterialFlags
      ensures this.encryptionContext == res.encryptionContext
      ensures this.algorithmSuiteID == res.algorithmSuiteID
      ensures res.plaintextDataKey.Some?
      ensures this.keyringTrace <= res.keyringTrace
      ensures this.verificationKey == res.verificationKey
    {
      var m := this.(plaintextDataKey := Some(plaintextDataKey), 
                     keyringTrace := this.keyringTrace + newTraceEntries);
      assert m.Valid();
      m
    }
  }

  type ValidDecryptionMaterials = i: DecryptionMaterials | i.Valid() witness DecryptionMaterials.ValidWitness()

  predicate method CompatibleDecryptionMaterials(m1: ValidDecryptionMaterials, m2: ValidDecryptionMaterials) {
    var generateTraces := Filter(m1.keyringTrace + m2.keyringTrace, IsGenerateTraceEntry);
    && m1.encryptionContext == m2.encryptionContext
    && m1.algorithmSuiteID == m2.algorithmSuiteID && m1.plaintextDataKey == m2.plaintextDataKey
    && |generateTraces| <= 1
    && (|generateTraces| == 1 ==> |m1.keyringTrace| > 0 && generateTraces[0] == m1.keyringTrace[0])
    && m1.verificationKey == m2.verificationKey
  }
}
