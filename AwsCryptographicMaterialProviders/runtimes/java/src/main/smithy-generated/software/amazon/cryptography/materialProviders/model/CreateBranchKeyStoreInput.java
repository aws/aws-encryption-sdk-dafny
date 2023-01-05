package software.amazon.cryptography.materialProviders.model;

import software.amazon.awssdk.services.dynamodb.DynamoDbClient;

public class CreateBranchKeyStoreInput {
    private final String tableName;

    private final DynamoDbClient ddbClient;

    protected CreateBranchKeyStoreInput(BuilderImpl builder) {
        this.tableName = builder.tableName();
        this.ddbClient = builder.ddbClient();
    }

    public String tableName() {
        return this.tableName;
    }

    public DynamoDbClient ddbClient() {
        return this.ddbClient;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder tableName(String tableName);

        String tableName();

        Builder ddbClient(DynamoDbClient ddbClient);

        DynamoDbClient ddbClient();

        CreateBranchKeyStoreInput build();
    }

    protected static class BuilderImpl implements Builder {
        protected String tableName;

        protected DynamoDbClient ddbClient;

        protected BuilderImpl() {
        }

        protected BuilderImpl(CreateBranchKeyStoreInput model) {
            this.tableName = model.tableName();
            this.ddbClient = model.ddbClient();
        }

        public Builder tableName(String tableName) {
            this.tableName = tableName;
            return this;
        }

        public String tableName() {
            return this.tableName;
        }

        public Builder ddbClient(DynamoDbClient ddbClient) {
            this.ddbClient = ddbClient;
            return this;
        }

        public DynamoDbClient ddbClient() {
            return this.ddbClient;
        }

        public CreateBranchKeyStoreInput build() {
            return new CreateBranchKeyStoreInput(this);
        }
    }
}