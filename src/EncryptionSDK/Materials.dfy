include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/UInt.dfy"
include "./AlgorithmSuite.dfy"

module Materials {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import AlgorithmSuite

  type EncryptionContext = seq<(seq<UInt8>, seq<UInt8>)>

  datatype EncryptedDataKey = EncryptedDataKey(providerID : string, 
                                               providerInfo : seq<UInt8>,
                                               ciphertext : seq<UInt8>)

  // TODO: Add keyring trace
  class EncryptionMaterials {
    var algorithmSuiteID: AlgorithmSuite.ID
    var encryptedDataKeys: seq<EncryptedDataKey>
    var encryptionContext: Option<EncryptionContext>
    var plaintextDataKey: Option<seq<UInt8>>
    var signingKey: Option<seq<UInt8>>

    predicate Valid() 
      reads this
    {
      |encryptedDataKeys| > 0 ==> plaintextDataKey.Some?
      // TODO data key length assurance
    }
    constructor(algorithmSuiteID: AlgorithmSuite.ID,
                encryptedDataKeys: seq<EncryptedDataKey>, 
                encryptionContext: Option<EncryptionContext>, 
                plaintextDataKey: Option<seq<UInt8>>,
                signingKey: Option<seq<UInt8>>)
      requires |encryptedDataKeys| > 0 ==> plaintextDataKey.Some?
      ensures Valid()
    {
      this.algorithmSuiteID := algorithmSuiteID;
      this.encryptedDataKeys := encryptedDataKeys;
      this.encryptionContext := encryptionContext;
      this.plaintextDataKey := plaintextDataKey;
      this.signingKey := signingKey;
    }

    method setPlaintextDataKey(dataKey: seq<UInt8>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures algorithmSuiteID == old(algorithmSuiteID)
      ensures encryptedDataKeys == old(encryptedDataKeys)
      ensures encryptionContext == old(encryptionContext)
      ensures signingKey == old(signingKey)
      ensures plaintextDataKey == Some(dataKey)
    {
      plaintextDataKey := Some(dataKey);
    }

    method appendEncryptedDataKeys(edk: EncryptedDataKey)
      requires Valid()
      requires plaintextDataKey.Some?
      modifies this
      ensures Valid()
      ensures plaintextDataKey == old(plaintextDataKey)
      ensures algorithmSuiteID == old(algorithmSuiteID)
      ensures encryptionContext == old(encryptionContext)
      ensures signingKey == old(signingKey)
      ensures |encryptedDataKeys| > 0
      ensures encryptedDataKeys[..|encryptedDataKeys|-1] == old(encryptedDataKeys)
    {
      encryptedDataKeys := encryptedDataKeys + [edk];
    }
  }

  // TODO: Add keyring trace
  class DecryptionMaterials {
    var algorithmSuiteID: AlgorithmSuite.ID
    var encryptionContext: Option<EncryptionContext>
    var plaintextDataKey: Option<seq<UInt8>>
    var verificationKey: Option<seq<UInt8>>
    
    // TODO add Valid()

    constructor(algorithmSuiteID: AlgorithmSuite.ID,
                encryptionContext: Option<EncryptionContext>,
                plaintextDataKey: Option<seq<UInt8>>,
                verificationKey: Option<seq<UInt8>>) {
      this.algorithmSuiteID := algorithmSuiteID;
      this.encryptionContext := encryptionContext;
      this.plaintextDataKey := plaintextDataKey;
      this.verificationKey := verificationKey;
    }

    method setPlaintextDataKey(dataKey: seq<UInt8>)
      modifies this
      ensures plaintextDataKey == Some(dataKey)
      ensures algorithmSuiteID == old(algorithmSuiteID)
      ensures encryptionContext == old(encryptionContext)
      ensures verificationKey == old(verificationKey)
    {
      plaintextDataKey := Some(dataKey);
    }
  }
}
