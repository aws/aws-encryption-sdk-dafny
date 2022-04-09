# Retrieve a signed assembly. The signing process may take some
# time, so we need to account for the case where the object does
# not yet exist


if [ "$#" -ne 2 ]; then
    echo "Usage: retrieve_signed_assembly.sh <target_framework> <unique_id>"
    exit 1
fi

TARGET=$1
UNIQUE_ID=$2

source ./codebuild/release/variables.sh

# Signed assemblies are suffixed with the signer job id, so we need
# to figure out the job id first
JOB_ID=$(./codebuild/release/get_job_id.sh $TARGET $UNIQUE_ID)

if [ -z $JOB_ID ]
then
    echo "Failed to retrieve signer job id, exiting"
    exit 1
fi

# Now retrieve the signed object, with retries
RETRY_COUNT=0
while [ $RETRY_COUNT -lt 3 ]
do
    aws --region $REGION \
        s3 cp \
        s3://$SIGNED_PREFIX/$TARGET/$ASSEMBLY_NAME-$UNIQUE_ID.dll-$JOB_ID \
        $RELEASE_FOLDER/$TARGET/$ASSEMBLY_NAME.dll
    retValue=$?
    if [ $retValue -ne 0 ]
    then
        RETRY_COUNT=$((RETRY_COUNT+1))
        echo "Signed object not found, retrying in 30 seconds"
        sleep 3
    else
        echo "Signed object successfully retrieved"
        exit 0
    fi
done

# If we got here it means we were never able to retrieve the signed object.
# Exit with a failure code
echo "Failed to retrieve signed object, exiting"
exit 1
