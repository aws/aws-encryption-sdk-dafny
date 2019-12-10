## Steps for enabling necessary KMS permissions:

When attempting to run `test/KMS/Integration.dfy`, you may encounter an error:

```
Amazon.Runtime.AmazonServiceException: Unable to get IAM security credentials from EC2 Instance Metadata Service.
```

This means you don't have the correct credentials to make the KMS calls required for the KMS integration test. To give your environment the correct permissions, you must add credentials to your environment.

### Outside of EC2

1. [Create an IAM user](https://docs.aws.amazon.com/IAM/latest/UserGuide/id_users_create.html) with programmatic access, and the following policy:
```
{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Sid": "VisualEditor0",
            "Effect": "Allow",
            "Action": [
                "kms:Decrypt",
                "kms:Encrypt",
                "kms:GenerateDataKey"
            ],
            "Resource": "*"
        }
    ]
}
```
2. Add the nely created credentials to your evironment using [`aws configure`](https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-configure.html).

### Inside EC2

1. [Create and attach an IAM role](https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/iam-roles-for-amazon-ec2.html) wit the following policy:
```
{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Sid": "VisualEditor0",
            "Effect": "Allow",
            "Action": [
                "kms:Decrypt",
                "kms:Encrypt",
                "kms:GenerateDataKey"
            ],
            "Resource": "*"
        }
    ]
}
```
