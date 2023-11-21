# Changelog

## 4.0.1

### Fixes

The ESDK-NET’s Message Header AAD
incorrectly appended two empty bytes
when using the DefaultCMM.
The HKDF invocation of non-committing algorithm suites
failed to include the Message ID in the info parameter.

Neither of these issues 
effect the security of messages 
written by the 4.0.0 release.

However, 
these messages diverge 
from the Encryption SDK Message Specification.
Thus:

* ESDK-NET v4.0.0 writes messages that only ESDK-NET v4.0.0 and greater can read.
* ESDK-NET v4.0.0 is ONLY able to read messages that are written by ESDK-NET v4.0.0

These issues are fixed in 4.0.1, 
which writes messages according to the Encryption SDK Message Specification,
and are interoperable with other implementations of this library.

The option NetV4_RetryPolicy can be use to decrypt v4.0.0 messages.
See [NetV4_0_0Example.cs](Examples/NetV4_0_0Example.cs) on how to use the NetV4_RetryPolicy
and details on distributed applications.


## 4.0.0

### BREAKING CHANGES

* AWS Encryption SDK for .NET now directly depends on the AWS Cryptographic Material Providers Library for .NET
* Required Encryption Context CMM generates messages that the Encryption SDK for .NET < 4.0.0 cannot read
 * This feature does not yet exist in other Encryption SDKs, as such, messages written using this feature are not interoperable
   with other runtimes.
* AWS Encryption SDK now only supports .NET 6.0 and later, and .NET Framework 4.8.0 and later.

### Features
* Required Encryption Context CMM
* AWS KMS RSA Keyring
* AWS KMS Hierarchical Keyring

### NuGet Rename
_Added on October 16th, 2023_
As of version 4.0.0, the AWS Encryption SDK for .NET is on NuGet as [AWS.Cryptography.EncryptionSDK](https://www.nuget.org/packages/AWS.Cryptography.EncryptionSDK).

Prior versions are under [AWS.EncryptionSDK](https://www.nuget.org/packages/AWS.EncryptionSDK).


## 3.1.0

### Fixes

* chore: pack README for display on NuGet page (<https://github.com/aws/aws-encryption-sdk-dafny/pull/585>)
* fix: add DiscoveryFilter to MRK Discovery Keyring example (<https://github.com/aws/aws-encryption-sdk-dafny/pull/581>)
* docs: fix .NET ESDK link in README (<https://github.com/aws/aws-encryption-sdk-dafny/pull/589>)
* docs: fix .NET ESDK package name in README (<https://github.com/aws/aws-encryption-sdk-dafny/pull/600>)
* docs: link to macOS setup wiki in README (<https://github.com/aws/aws-encryption-sdk-dafny/pull/601>)

### Maintenance

* chore: update generated KMS code (<https://github.com/aws/aws-encryption-sdk-dafny/pull/580>)
* chore: use public spec URL for submodule (<https://github.com/aws/aws-encryption-sdk-dafny/pull/586>)
* fix: use renamed directories for Duvet report (<https://github.com/aws/aws-encryption-sdk-dafny/pull/587>)
* chore: bump Newtonsoft.Json in test vector projects (<https://github.com/aws/aws-encryption-sdk-dafny/pull/595>)
* feat: add user agent to default KMS clients (<https://github.com/aws/aws-encryption-sdk-dafny/pull/598>)
* chore: address potential unsoundness (dafny-lang/dafny#2500) (<https://github.com/aws/aws-encryption-sdk-dafny/pull/599>)
* ci: use .NET 6.0 for release buildspecs (<https://github.com/aws/aws-encryption-sdk-dafny/pull/602>)

## 3.0.0 (2022-05-17)

Initial launch of the AWS Encryption SDK for .NET.
