package software.amazon.cryptography.materialProviders.model;

public class VersionBranchKeyOutput {
    private final Integer versionCreated;

    protected VersionBranchKeyOutput(BuilderImpl builder) {
        this.versionCreated = builder.versionCreated();
    }

    public Integer versionCreated() {
        return this.versionCreated;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder versionCreated(Integer versionCreated);

        Integer versionCreated();

        VersionBranchKeyOutput build();
    }

    protected static class BuilderImpl implements Builder {
        protected Integer versionCreated;

        protected BuilderImpl() {
        }

        protected BuilderImpl(VersionBranchKeyOutput model) {
            this.versionCreated = model.versionCreated();
        }

        public Builder versionCreated(Integer versionCreated) {
            this.versionCreated = versionCreated;
            return this;
        }

        public Integer versionCreated() {
            return this.versionCreated;
        }

        public VersionBranchKeyOutput build() {
            return new VersionBranchKeyOutput(this);
        }
    }
}
