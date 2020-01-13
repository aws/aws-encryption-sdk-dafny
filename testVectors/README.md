This directory holds dafny and C# code which decrypts the kms test vectors in https://github.com/awslabs/aws-encryption-sdk-test-vectors

Download and unzip a set of vectors.

Set the DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH environment variable as the absolute path of the manifest to use.

```
export DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH="<absolute_path_to_manifest>"
```

To run the test vectors from this directory, run the following command:

```
dotnet test
```

To run the test vectors from the base directory, run the following command:

```
dotnet test testVectors
```
