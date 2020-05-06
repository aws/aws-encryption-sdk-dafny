# AWS Encryption SDK for .NET Examples

This section features examples that show you
how to use the AWS Encryption SDK.
We demonstrate how to use the encryption and decryption APIs
and how to set up some common configuration patterns.

## APIs

The AWS Encryption SDK provides two high-level APIs:
one-step APIs that process the entire operation in memory
and streaming APIs.

You can find examples that demonstrate these APIs
in the [`examples/dotnet/`](./) directory.

* [How to encrypt and decrypt](./) *TODO*
* [How to change the algorithm suite](./) *TODO*
* [How to encrypt and decrypt data streams in memory](./) *TODO*
* [How to encrypt and decrypt data streamed between files](./) *TODO*

## Configuration

To use the encryption and decryption APIs,
you need to describe how you want the library to protect your data keys.
You can do this by configuring
[keyrings](#keyrings) or [cryptographic materials managers](#cryptographic-materials-managers).
These examples will show you how to use the configuration tools that we include for you
and how to create some of your own.
We start with AWS KMS examples, then show how to use other wrapping keys.

* Using AWS Key Management Service (AWS KMS)
    * [How to use one AWS KMS CMK](./) *TODO*
    * [How to use multiple AWS KMS CMKs in different regions](./) *TODO*
    * [How to decrypt when you don't know the CMK](./) *TODO*
    * [How to decrypt within a region](./) *TODO*
    * [How to decrypt with a preferred region but failover to others](./) *TODO*
    * [How to reproduce the behavior of an AWS KMS master key provider](./) *TODO*
* Using raw wrapping keys
    * [How to use a raw AES wrapping key](./keyrings/RawRSAKeyring/RawAESKeyringExample.cs)
    * [How to use a raw RSA wrapping key](./) *TODO*
    * [How to use a raw RSA wrapping key when the key is PEM or DER encoded](./) *TODO*
    * [How to encrypt with a raw RSA public key wrapping key without access to the private key](./) *TODO*
* Combining wrapping keys
    * [How to combine AWS KMS with an offline escrow key](./) *TODO*
* How to reuse data keys across multiple messages
    * [with the caching cryptographic materials manager](./) *TODO*
* How to restrict algorithm suites
    * [with a custom cryptographic materials manager](./) *TODO*
* How to require encryption context fields
    * [with a custom cryptographic materials manager](./) *TODO*

### Keyrings

Keyrings are the most common way for you to configure the AWS Encryption SDK.
They determine how the AWS Encryption SDK protects your data.
You can find these examples in [`examples/dotnet/keyrings`](./keyring).

### Cryptographic Materials Managers

Keyrings define how your data keys are protected,
but there is more going on here than just protecting data keys.

Cryptographic materials managers give you higher-level controls
over how the AWS Encryption SDK protects your data.
This can include things like
enforcing the use of certain algorithm suites or encryption context settings,
reusing data keys across messages,
or changing how you interact with keyrings.
You can find these examples in
[`examples/dotnet/CryptoMaterialsManager`](./CryptoMaterialsManager).

# Writing Examples

If you want to contribute a new example, that's awesome!
To make sure that your example is tested in our CI,
please make sure that it meets the following requirements:

1. The example MUST be a distinct module in the [`examples/dotnet/`](./) directory.
1. The example MAY be nested arbitrarily deeply.
1. Each example file MUST contain exactly one example.
1. Each example filename MUST be descriptive.
1. Each example file MUST contain a public class matching the filename.
1. Each example file MUST contain a method called `run` that runs the example.
1. Each example MUST be exercised by a `[Fact]` test method within its class.
