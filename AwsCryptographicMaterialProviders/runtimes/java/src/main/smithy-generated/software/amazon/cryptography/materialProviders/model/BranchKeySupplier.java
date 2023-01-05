package software.amazon.cryptography.materialProviders.model;

public interface BranchKeySupplier {
    public String getBranchKey(GetBranchKeyInput input);
}