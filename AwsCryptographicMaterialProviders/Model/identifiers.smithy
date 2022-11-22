namespace aws.cryptography.materialProviders

/////////////
// Commitment

//= aws-encryption-sdk-specification/framework/commitment-policy.md#supported-library-commitment-policy-enum
//= type=implication
//# The Material Providers Library MUST provide
//# a distinct commitment policy ENUM for each library.

//= aws-encryption-sdk-specification/framework/commitment-policy.md#supported-library-commitment-policy-enum
//= type=implication
//# | ESDK Commitment Policy ENUM     |
//# | ------------------------------- |
//# | FORBID_ENCRYPT_ALLOW_DECRYPT    |
//# | REQUIRE_ENCRYPT_ALLOW_DECRYPT   |
//# | REQUIRE_ENCRYPT_REQUIRE_DECRYPT |
@enum([
  {
    name: "FORBID_ENCRYPT_ALLOW_DECRYPT",
    value: "FORBID_ENCRYPT_ALLOW_DECRYPT",
  },
  {
    name: "REQUIRE_ENCRYPT_ALLOW_DECRYPT",
    value: "REQUIRE_ENCRYPT_ALLOW_DECRYPT",
  },
  {
    name: "REQUIRE_ENCRYPT_REQUIRE_DECRYPT",
    value: "REQUIRE_ENCRYPT_REQUIRE_DECRYPT",
  },
])
string ESDKCommitmentPolicy

//= aws-encryption-sdk-specification/framework/commitment-policy.md#supported-commitment-policy-enum
//= type=implication
//# This means that different libraries MAY have duplicate Library Commitment Policy ENUM.

//= aws-encryption-sdk-specification/framework/commitment-policy.md#supported-commitment-policy-enum
//= type=implication
//# The Material Providers Library also MUST provide
//# a union ENUM for all distinct commitment policy ENUMs
//# called the Commitment Policy ENUM.
union CommitmentPolicy {
  ESDK: ESDKCommitmentPolicy
}

//////////
// Padding

// Values come from: https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/framework/raw-rsa-keyring.md#supported-padding-schemes
@enum([
  {
    name: "PKCS1",
    value: "PKCS1",
  },
  {
    name: "OAEP_SHA1_MGF1",
    value: "OAEP_SHA1_MGF1",
  },
  {
    name: "OAEP_SHA256_MGF1",
    value: "OAEP_SHA256_MGF1",
  },
  {
    name: "OAEP_SHA384_MGF1",
    value: "OAEP_SHA384_MGF1",
  },
  {
    name: "OAEP_SHA512_MGF1",
    value: "OAEP_SHA512_MGF1",
  },
])
string PaddingScheme

//////////////////////////
// AES wrapping algorithms
@enum([
  {
    name: "ALG_AES128_GCM_IV12_TAG16",
    value: "ALG_AES128_GCM_IV12_TAG16",
  },
  {
    name: "ALG_AES192_GCM_IV12_TAG16",
    value: "ALG_AES192_GCM_IV12_TAG16",
  },
  {
    name: "ALG_AES256_GCM_IV12_TAG16",
    value: "ALG_AES256_GCM_IV12_TAG16",
  },
])
string AesWrappingAlg
