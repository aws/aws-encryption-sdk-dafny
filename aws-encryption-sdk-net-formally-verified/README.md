# AWS Encryption SDK for .NET

![Build Status - master branch](https://codebuild.us-west-2.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiVmIzeGwwQmY5bXdMQXg2aVBneWtDc3FHSWRHTjYrNnVUem9nNXJFUmY2Rk1yRnJvSjJvK3JCL2RScFRjSVF1UjA1elR3L0xpTVpiNmRZS0RyWjJpTnBFPSIsIml2UGFyYW1ldGVyU3BlYyI6InBBQm1tT1BPNjB3RU9XUS8iLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=master)

AWS Encryption SDK for .NET

[Security issue notifications](./CONTRIBUTING.md#security-issue-notifications)

## Using the AWS Encryption SDK for .NET
The AWS Encryption SDK is available on [NuGet](https://www.nuget.org/) and can referenced from an existing `.csproj` through typical ways.

```
<!-- TODO: Update with actual NuGet package name, the name below is just an example -->
<PackageReference Include="AWS.EncryptionSDK" />
```

The Encryption SDK source has a target framework of [netstandard2.0](https://docs.microsoft.com/en-us/dotnet/standard/net-standard).

## Building the AWS Encryption SDK for .NET

To build, the AWS Encryption SDK requires the most up to date version of [dafny](https://github.com/dafny-lang/dafny) on your PATH.

The Encryption SDK source has a target framework of [netstandard2.0](https://docs.microsoft.com/en-us/dotnet/standard/net-standard).
Tests and test vectors have a target framework of [netcoreapp3.0](https://docs.microsoft.com/en-us/dotnet/standard/frameworks), which is required for properly building and running tests.
Therefore, building and verifying requires [dotnet 3.0](https://dotnet.microsoft.com/download/dotnet-core/3.0).

You will also need to ensure that you fetch all submodules using either `git clone --recursive ...` when cloning the repository or `git submodule update --init` on an existing clone.

To build all source files into one dll:

```
dotnet build
```

### (Optional) Set up the AWS Encryption SDK to work with AWS KMS

If you set up the AWS Encryption SDK to use the AWS KMS Keyring,
the AWS Encryption SDK will make calls to AWS KMS on your behalf,
using the appropriate AWS SDK.

However, you must first set up AWS credentials for use with the AWS SDK. 
Instructions for setting up AWS credentials are available in the [AWS Docs for the AWS SDK for .NET.](https://docs.aws.amazon.com/sdk-for-net/v3/developer-guide/net-dg-config-creds.html).

## Testing the AWS Encryption SDK for .NET

### Configure AWS credentials

To run the test suite you must first set up AWS credentials for use with the AWS SDK.
This is required in order to run the integration tests, which use a KMS Keyring against a publically accessible KMS CMK.

Instructions for setting up AWS credentials are available in the [AWS Docs for the AWS SDK for .NET](https://docs.aws.amazon.com/sdk-for-net/v3/developer-guide/net-dg-config-creds.html).

### Run the tests

Run the test suite with:

```
dotnet test
```

You can see more detail about what test cases are being run by increasing the verbosity:

```
dotnet test --logger:"console;verbosity=normal"
```

Run the test vector suite after [set up](TestVectors/README.md) with:

```
dotnet test TestVectors
```

Run tests on examples, to ensure they are up to date:

```
dotnet test Examples
```

Please note that tests and test vectors require internet access and valid AWS credentials, since calls to KMS are made as part of the test workflow.

### Generate decryption test vectors

See the [TestVectorGenerator README](TestVectorGenerator/README.md).

### Generate code coverage results

From the Test/ directory, you can generate a coverage.cobertura.xml file 
containing code coverage results to the Test/TestResults/ directory with:

```
dotnet test --collect:"XPlat Code Coverage" --settings ../runsettings.xml
```

We use [Coverlet](https://github.com/coverlet-coverage/coverlet) for our code coverage. 
For a list of Coverlet commands/additional options, 
please see the following [usage guide](https://github.com/coverlet-coverage/coverlet#usage).

We use [ReportGenerator](https://github.com/danielpalme/ReportGenerator) to visualize code coverage.

Install ReportGenerator with:

```
dotnet new tool-manifest
```
```
dotnet tool install dotnet-reportgenerator-globaltool
```

From Source/, generate a human readable index.html file of our code coverage to Test/TestResults/ with:

```
dotnet reportgenerator
"-reports:../Test/TestResults/coverage.cobertura.xml" 
"-targetdir:../Test/TestResults"
```

To view the code coverage report, open the index.html file in any browser.

## License

This library is licensed under the Apache 2.0 License.
