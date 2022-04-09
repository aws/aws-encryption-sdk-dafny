#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "Usage: upload_assembly.sh <target_framework> <unique_id>"
    exit 1
fi

TARGET=$1
UNIQUE_ID=$2

source ./codebuild/release/variables.sh

# Upload the assembly to the unsigned bucket
aws --region $REGION \
    s3 cp \
    $RELEASE_FOLDER/$TARGET/$ASSEMBLY_NAME.dll \
    s3://$UNSIGNED_PREFIX/$TARGET/$ASSEMBLY_NAME-$UNIQUE_ID.dll \
    --acl bucket-owner-full-control

if [ $? -ne 0 ]; then
    echo "Failed to upload object, exiting"
    exit 1
fi

