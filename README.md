# AWS Encryption SDK for Dafny

![Build Status - master branch](https://codebuild.us-west-2.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiVmIzeGwwQmY5bXdMQXg2aVBneWtDc3FHSWRHTjYrNnVUem9nNXJFUmY2Rk1yRnJvSjJvK3JCL2RScFRjSVF1UjA1elR3L0xpTVpiNmRZS0RyWjJpTnBFPSIsIml2UGFyYW1ldGVyU3BlYyI6InBBQm1tT1BPNjB3RU9XUS8iLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=master)

[//]: # (Status for the static-analysis workflow on push events to the "develop" branch)

![static analysis](https://github.com/awslabs/aws-encryption-sdk-dafny/workflows/static%20analysis/badge.svg?branch=develop&event=push)

AWS Encryption SDK for Dafny

[Security issue notifications](./CONTRIBUTING.md#security-issue-notifications)

## Building the AWS Encryption SDK for Dafny

To build, the AWS Encryption SDK requires the most up to date version of [dafny](https://github.com/dafny-lang/dafny) on your PATH.
In addition, this project uses the parallel verification tasks provided by the [dafny.msbuild](https://github.com/dafny-lang/dafny.msbuild) MSBuild plugin,
and thus requires [dotnet 3.0](https://dotnet.microsoft.com/download/dotnet-core/3.0).

To run the dafny verifier across all files:

```
# Currently, test depends on src, so verifying test will also verify src
dotnet build -t:VerifyDafny test
```

The tests currently require native implementations of cryptographic primitives and other methods, 
so they can only be run when embedding this library into one of the compilation target languages supported by Dafny:

- [.NET](https://github.com/awslabs/aws-encryption-sdk-net)

## License

This library is licensed under the Apache 2.0 License.
