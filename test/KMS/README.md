## Steps for enabling necessary KMS permissions:

When attempting to run `test/KMS/Integration.dfy`, you may encounter an error:

```
Amazon.Runtime.AmazonServiceException: Unable to get IAM security credentials from EC2 Instance Metadata Service.
```

This is because the test environment does not have access to KMS permissions. Here is how to configure you credentials.

- Open the AWS console, and navigate to IAM
- Create an IAM user
    - Give the user a name (i.e. “ESDK-Dafny-user”)
    - Programatic access
    - Next
    - Attach existing policy
        - Create new policy
            - KMS
            - Write
                - Generate datakey
                - Encrypt
                - Decrypt
            - All resources
            - Give the policy a name (I.e. “ESDK-minimum”)
        - Go back to last browser tab
        - Refresh the policy menu (not the page)
        - Attach the policy you made
    - Tags
    - Review
    - Create User
        - Save the Copy Access Key, Secret Key

Create a file in `~/.aws/credentials`, and write your keys to it so it looks like this:

```
[default]
aws_access_key_id=YOUR_ACCESS_KEY
aws_secret_access_key=YOUR_SECRET_KEY
```
