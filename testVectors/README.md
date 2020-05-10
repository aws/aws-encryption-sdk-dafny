This directory contains a test harness that exercises a set of test vectors against the AWS Encryption SDK for .NET.

Test vectors are available at https://github.com/awslabs/aws-encryption-sdk-test-vectors.
Information about the test vector manifests can be found at https://github.com/awslabs/aws-crypto-tools-test-vector-framework.

## Set Up

### Configure AWS credentials

To run the test vectors you must first set up AWS credentials for use with the AWS SDK for .NET.
This is required in order to test the KMS Keyring using a publicaly accessible KMS CMK.

Instructions for setting up AWS credentials for the AWS SDK for .NET can be found at https://docs.aws.amazon.com/sdk-for-net/v3/developer-guide/net-dg-config-creds.html.

### Configure the test vectors

Download and unzip a set of vectors from https://github.com/awslabs/aws-encryption-sdk-test-vectors.

Set the DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH environment variable as the absolute path of the manifest to use.

```
export DAFNY_AWS_ESDK_TEST_VECTOR_MANIFEST_PATH="<absolute_path_to_manifest>"
```

Set the DAFNY_AWS_ESDK_DECRYPT_ORACLE_URL environment variable to the AWS Crypto Tools provided api endpoint.

```
export DAFNY_AWS_ESDK_DECRYPT_ORACLE_URL="http://xi1mwx3ttb.execute-api.us-west-2.amazonaws.com/api/v0/decrypt"
```

## Run

To run the test vectors from this directory, run the following command:

```
dotnet test
```

To run the test vectors from the base directory, run the following command:

```
dotnet test testVectors
```
