This is the KMS smithy model, but with a couple adjustments:

- `com.amazonaws.kms#TrentService` is renamed to `com.amazonaws.kms#KeyManagementService`.
- The `ListKeys` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
    - This is because the Dafny compiler does not allow "Keys" as a constructor parameter name.
      See <https://github.com/dafny-lang/dafny/issues/1587>.
- The `ListKeysResponse` structure is removed from the model.
    - This is for the same reason as removing `ListKeys`.
- The `ListRetirableGrants` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
    - This is because its output shape is represented inconsistently in the .NET AWS SDK.
