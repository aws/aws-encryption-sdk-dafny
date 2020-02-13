include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "KeyDerivationAlgorithms"} KeyDerivationAlgorithms {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  // See Key Derivation Algorithm
  // https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/algorithms-reference.html
  datatype {:extern "KeyDerivationAlgorithm"} KeyDerivationAlgorithm = HKDF_WITH_SHA_384 | HKDF_WITH_SHA_256 | IDENTITY

  type {:extern "HKDFAlgorithms"} HKDFAlgorithms = a: KeyDerivationAlgorithm | a != KeyDerivationAlgorithm.IDENTITY witness KeyDerivationAlgorithm.HKDF_WITH_SHA_384
  type IdentityAlgorithm = a: KeyDerivationAlgorithm | a == KeyDerivationAlgorithm.IDENTITY witness KeyDerivationAlgorithm.IDENTITY
}
