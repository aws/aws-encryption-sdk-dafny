package software.amazon.cryptography.materialProviders.model;

public class CreateBranchKeyOutput {
    private final String branchKeyId;

    protected CreateBranchKeyOutput(BuilderImpl builder) {
        this.branchKeyId = builder.branchKeyId();
    }

    public String branchKeyId() {
        return this.branchKeyId;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder branchKeyId(String branchKeyId);

        String branchKeyId();

        CreateBranchKeyOutput build();
    }

    protected static class BuilderImpl implements Builder {
        protected String branchKeyId;

        protected BuilderImpl() {
        }

        protected BuilderImpl(CreateBranchKeyOutput model) {
            this.branchKeyId = model.branchKeyId();
        }

        public Builder branchKeyId(String branchKeyId) {
            this.branchKeyId = branchKeyId;
            return this;
        }

        public String branchKeyId() {
            return this.branchKeyId;
        }

        public CreateBranchKeyOutput build() {
            return new CreateBranchKeyOutput(this);
        }
    }
}
