This is the KMS smithy model, but with a couple adjustments:

- `com.amazonaws.kms#TrentService` is renamed to `com.amazonaws.kms#KeyManagementService`.
- The `ListKeysResponse` structure is removed from the model.
- The `ListKeys` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
