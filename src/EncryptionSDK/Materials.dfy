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
  datatype EncryptionMaterials = EncryptionMaterials(algorithmSuiteID : AlgorithmSuite.ID,
                                                     encryptedDataKeys : seq<EncryptedDataKey>, 
                                                     encryptionContext : EncryptionContext, 
                                                     plaintextDataKey : Option<seq<UInt8>>,
                                                     signingKey : Option<seq<UInt8>>) {
    predicate Valid() {
      |this.encryptedDataKeys| > 0 ==> this.plaintextDataKey.Some?
      // TODO data key length assurance
    }
  }

  // TODO: Add keyring trace
  datatype DecryptionMaterials = DecryptionMaterials(algorithmID : AlgorithmSuite.ID,
                                                     encryptionContext : EncryptionContext,
                                                     plaintextDataKey : Option<seq<UInt8>>,
                                                     verificationKey : Option<seq<UInt8>>)
}