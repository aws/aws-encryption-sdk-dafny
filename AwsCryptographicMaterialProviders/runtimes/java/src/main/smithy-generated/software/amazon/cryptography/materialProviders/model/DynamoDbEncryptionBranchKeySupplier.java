package software.amazon.cryptography.materialProviders.model;

// TODO this is currently modelled as belonging to the MPL,
// however it may make more sense to move it to DynamoDbEncryption,
// or rename it.
public class DynamoDbEncryptionBranchKeySupplier implements BranchKeySupplier {
    public DynamoDbEncryptionBranchKeySupplier() {}

    public String getBranchKey(GetBranchKeyInput input) {
        // Currently stubbed.
        // When implemented this will take in a BranchKeyFromItemSupplier
        // and wrap around that behavior, performing the transformation of the serialized
        // item attributes in the context to a Map<String, AttributeValue>
        return "foobar";
    }
}