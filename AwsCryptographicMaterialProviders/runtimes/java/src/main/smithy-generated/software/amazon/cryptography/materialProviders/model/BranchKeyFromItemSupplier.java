package software.amazon.cryptography.materialProviders.model;

public interface BranchKeyFromItemSupplier {
    public String getBranchKeyFromItem(GetBranchKeyFromItemInput input);
}
