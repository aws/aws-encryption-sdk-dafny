package software.amazon.cryptography.materialProviders.model;

import software.amazon.awssdk.services.dynamodb.model.TableDescription;

public class CreateBranchKeyStoreOutput {
    private final TableDescription tableDescription;

    protected CreateBranchKeyStoreOutput(BuilderImpl builder) {
        this.tableDescription = builder.tableDescription();
    }

    public TableDescription tableDescription() {
        return this.tableDescription;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder tableDescription(TableDescription tableDescription);

        TableDescription tableDescription();

        CreateBranchKeyStoreOutput build();
    }

    protected static class BuilderImpl implements Builder {
        protected TableDescription tableDescription;

        protected BuilderImpl() {
        }

        protected BuilderImpl(CreateBranchKeyStoreOutput model) {
            this.tableDescription = model.tableDescription();
        }

        public Builder tableDescription(TableDescription tableDescription) {
            this.tableDescription = tableDescription;
            return this;
        }

        public TableDescription tableDescription() {
            return this.tableDescription;
        }

        public CreateBranchKeyStoreOutput build() {
            return new CreateBranchKeyStoreOutput(this);
        }
    }
}
