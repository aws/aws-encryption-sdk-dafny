import argparse
import os
import time
import json

import boto3
from botocore.config import Config

RELEASE_FOLDER = "runtimes/net/bin/Release"
ASSEMBLY_NAME = "AWS.Cryptography.EncryptionSDK.dll"
REGION = "us-west-2"

# Variables to make it easier to reference our S3 objects
UNSIGNED_BUCKET = "esdk-365847122878-unsigned-bucket"
SIGNED_BUCKET = "esdk-365847122878-signed-bucket"
KEY_PREFIX = "aws_encryption_sdk_net/AuthenticodeSigner-SHA256-RSA"

CONFIG = Config(region_name = REGION)

# Role which provides access to our signed and unsigned buckets
ARTIFACT_ACCESS_ROLE_ARN = "arn:aws:iam::365847122878:role/EncryptionSDKNetV4CodeSigning-ArtifactAccessRole"

# Constants for accessing our API key
API_KEY_ROLE_ARN = "arn:aws:iam::582595803497:role/aws-crypto-tools-build-role"
API_KEY_SECRET_ARN = "arn:aws:secretsmanager:us-west-2:582595803497:secret:production/build/aws-crypto-tools-nuget-api-key-7ZY4pe"


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--target',
        required=True,
        metavar='t',
        type=str,
        help='The framework to target'
    )
    parser.add_argument(
        '--unique-id',
        required=True,
        metavar='u',
        type=str,
        help='A unique identifier for this signing flow'
    )
    parser.add_argument(
        '--output',
        required=False,
        metavar='o',
        type=str,
        help='Place to put output files'
    )
    return parser.parse_args()


def assume_artifact_access_role():
    """
    Assumes the role that is allowed to access the s3 buckets where
    unsigned objects should be placed and signed objects should be
    retrieved from.
    """
    sts = boto3.client("sts", config=CONFIG)

    creds = sts.assume_role(
        RoleArn=ARTIFACT_ACCESS_ROLE_ARN,
        RoleSessionName="CodeBuildRelease",
        ExternalId="EncryptionSDKNetV4CodeSigning",
    )

    return creds

def assume_api_key_role():
    """
    Assumes the role that is allowed to access the Nuget API key
    """
    sts = boto3.client("sts", config=CONFIG)

    creds = sts.assume_role(
        RoleArn=API_KEY_ROLE_ARN,
        RoleSessionName="CodeBuildRelease",
    )

    return creds


def get_s3_client(creds=None):
    """
    Returns an S3 client. Uses the given creds if provided, otherwise uses
    the IAM role that allows access to our signing artifacts.
    """
    if not creds:
        creds = assume_artifact_access_role()

    return boto3.client(
        "s3",
        config=CONFIG,
        aws_access_key_id = creds['Credentials']['AccessKeyId'],
        aws_secret_access_key = creds['Credentials']['SecretAccessKey'],
        aws_session_token = creds['Credentials']['SessionToken'],
    )


def upload_assembly(args, s3=None):
    """
    Uploads an unsigned assembly to the unsigned object bucket.
    """
    print(f"Uploading assembly with params: {args.target}, {args.unique_id}")
    if not s3:
        s3 = get_s3_client()

    source_object = os.path.join(RELEASE_FOLDER, args.target, ASSEMBLY_NAME)
    if not os.path.exists(source_object):
        raise Exception(f"File {source_object} does not exist")

    with open(source_object, 'br') as source_object_data:
        s3_key = "/".join([KEY_PREFIX, args.target, f"{args.unique_id}-{ASSEMBLY_NAME}"])

        result = s3.put_object(
            Bucket=UNSIGNED_BUCKET,
            Key=s3_key,
            Body=source_object_data,
            ACL="bucket-owner-full-control",
        )
        print(f"Successfully uploaded file {source_object} to {UNSIGNED_BUCKET}/{s3_key}")


def get_job_id(args, s3=None):
    """
    Gets the signer job id of the job that is signing a given artifact

    This job id is added as a tag to the original uploaded S3 object, so
    we query the tags for the appropriate key.
    """
    print(f"Getting job id with params: {args.target}, {args.unique_id}")
    if not s3:
        s3 = get_s3_client()

    s3_key = "/".join([KEY_PREFIX, args.target, f"{args.unique_id}-{ASSEMBLY_NAME}"])
    print(f"Searching for key {s3_key}")

    retry_count = 0
    while retry_count < 3:
        try:
            tags = s3.get_object_tagging(
                Bucket=UNSIGNED_BUCKET,
                Key=s3_key,
            )['TagSet']
            return next(item for item in tags if item['Key'] == 'signer-job-id')['Value']
        except Exception as e:
            print(f"Failed to get job id due to exception: {e}")
            time.sleep(10)
            retry_count += 1

    raise Exception(f"Could not find signer job id after {retry_count} attempts, stopping")


def retrieve_signed_assembly(args, s3=None):
    """
    Retrieves a signed assembly from the signed bucket
    """
    print(f"Retrieving signed assembly with params: {args.target}, {args.unique_id}")
    if not s3:
        s3 = get_s3_client()

    job_id = get_job_id(args, s3=s3)
    print(f"Found signer job id: {job_id}")

    object_name = f"{args.unique_id}-{ASSEMBLY_NAME}-{job_id}"

    s3_key = "/".join([KEY_PREFIX, args.target, object_name])

    retry_count = 0
    while retry_count < 3:
        try:
            signed_object = s3.get_object(
                Bucket=SIGNED_BUCKET,
                Key=s3_key,
            )
            if not args.output:
                destination_object = os.path.join(RELEASE_FOLDER, args.target, ASSEMBLY_NAME)
            else:
                destination_object = os.path.join(args.output, ASSEMBLY_NAME)
            with open(destination_object, 'wb') as destination_file:
                destination_file.write(signed_object['Body'].read())
            print(f"Wrote signed assembly to {destination_object}")
            
            return
        except Exception as e:
            print(f"Failed to retrieve signed object due to exception: {e}")
            time.sleep(10)
            retry_count += 1

    raise Exception(f"Could not retrieve signed object after {retry_count} attempts, stopping")


def retrieve_api_access_key():
    """
    Retrieves the API key used to access Nuget
    """

    creds = assume_api_key_role()

    client = boto3.client(
        "secretsmanager",
        config=CONFIG,
        aws_access_key_id = creds['Credentials']['AccessKeyId'],
        aws_secret_access_key = creds['Credentials']['SecretAccessKey'],
        aws_session_token = creds['Credentials']['SessionToken'],
    )

    response = client.get_secret_value(SecretId=API_KEY_SECRET_ARN)

    # Secrets Manager returns our secret value as a string containing json, i.e. '{"Key" : "Value"}'
    # We need the value, so we parse it as json so we can easily grab it
    parsed_secret = json.loads(response['SecretString'])
    return parsed_secret['Key']

