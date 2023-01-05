package software.amazon.cryptography.materialProviders.model;

public class CreateDynamoDbEncryptionBranchKeySupplierInput {
    private final BranchKeyFromItemSupplier branchKeyFromItemSupplier;

    protected CreateDynamoDbEncryptionBranchKeySupplierInput(BuilderImpl builder) {
        this.branchKeyFromItemSupplier = builder.branchKeyFromItemSupplier();
    }

    public BranchKeyFromItemSupplier branchKeyFromItemSupplier() {
        return this.branchKeyFromItemSupplier;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder branchKeyFromItemSupplier(BranchKeyFromItemSupplier branchKeyFromItemSupplier);

        BranchKeyFromItemSupplier branchKeyFromItemSupplier();

        CreateDynamoDbEncryptionBranchKeySupplierInput build();
    }

    protected static class BuilderImpl implements Builder {
        protected BranchKeyFromItemSupplier branchKeyFromItemSupplier;

        protected BuilderImpl() {
        }

        protected BuilderImpl(CreateDynamoDbEncryptionBranchKeySupplierInput model) {
            this.branchKeyFromItemSupplier = model.branchKeyFromItemSupplier();
        }

        public Builder branchKeyFromItemSupplier(
                BranchKeyFromItemSupplier branchKeyFromItemSupplier) {
            this.branchKeyFromItemSupplier = branchKeyFromItemSupplier;
            return this;
        }

        public BranchKeyFromItemSupplier branchKeyFromItemSupplier() {
            return this.branchKeyFromItemSupplier;
        }

        public CreateDynamoDbEncryptionBranchKeySupplierInput build() {
            return new CreateDynamoDbEncryptionBranchKeySupplierInput(this);
        }
    }
}