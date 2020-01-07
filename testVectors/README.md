This directory holds dafny and C# code which decrypts the kms test vectors in https://github.com/awslabs/aws-crypto-tools-test-vector-framework

To run the tests, download and unzip a set of vectors into the `data` directory.

Set the relative path to the manifest to use as part as the DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH environment variable.
This file must be located within the `data` directory, and all files referenced in the manifest must also exist in the `data` directory.

```
export DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH="data/manifest.json"
```

To run the test vectors, run the following command:

```
dotnet test
```
