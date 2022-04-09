# Get the signing job id. An asynchronous worker is adding the job id as
# a tag to the s3 object we just uploaded, so we need to handle the case where
# it doesn't yet exist

if [ "$#" -ne 2 ]; then
    echo "Usage: get_job_id.sh <target_framework> <unique_id>"
    exit 1
fi

TARGET=$1
UNIQUE_ID=$2

source ./codebuild/release/variables.sh

JOB_ID=
RETRY_COUNT=0

while [ $RETRY_COUNT -lt 3 ]
do
    JOB_ID=$(aws --region $REGION \
                 s3api get-object-tagging \
                 --bucket $UNSIGNED_BUCKET \
                 --key $KEY_PREFIX/$TARGET/$ASSEMBLY_NAME-$UNIQUE_ID.dll \
                 --query "TagSet[?Key=='signer-job-id'].Value" --output text)
    if [ -z $JOB_ID ]
    then
        RETRY_COUNT=$((RETRY_COUNT+1))
        sleep 3
    else
        echo $JOB_ID
        exit 0
    fi
done

# If we got here it means we were never able to retrieve the job id.
# Exit with a failure code
exit 1
