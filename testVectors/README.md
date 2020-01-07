This directory holds dafny and C# code which decrypts the kms test vectors in https://github.com/awslabs/aws-crypto-tools-test-vector-framework

To run the tests, download and unzip a set of vectors into the `data` directory.

Then run the following command:

```
dotnet test
```

In order to run the test vectors, the test vector manifest must exist at `data/manifest.json`, and all files referenced in the manifest must be relative to the `data` directory.
