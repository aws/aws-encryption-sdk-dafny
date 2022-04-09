# Common variables for signing/releasing

export RELEASE_FOLDER=Source/bin/Release 
export ASSEMBLY_NAME=AWS.EncryptionSDK
export REGION=us-west-2

# Variables to make it easier to reference our S3 objects
export UNSIGNED_BUCKET=349032751102-unsigned-bucket
export SIGNED_BUCKET=349032751102-signed-bucket
export KEY_PREFIX=aws_encryption_sdk_net/AuthenticodeSigner-SHA256-RSA
export UNSIGNED_PREFIX=$UNSIGNED_BUCKET/$KEY_PREFIX
export SIGNED_PREFIX=$SIGNED_BUCKET/$KEY_PREFIX

