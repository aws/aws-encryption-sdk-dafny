This is the [KMS smithy model](https://github.com/aws/aws-models/blob/a7e23cbfde9a5fc0b52c78ff969d72bfb8d8b6f8/kms/smithy/model.json),
but with a couple adjustments:

- The `ListKeys` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
    - This is because the Dafny compiler does not allow "Keys" as a constructor parameter name.
      See <https://github.com/dafny-lang/dafny/issues/1587>.
- The `ListKeysResponse` structure is removed from the model.
    - This is for the same reason as removing `ListKeys`.
- The `ListRetirableGrants` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
    - This is because its output shape is represented inconsistently in the .NET AWS SDK.
