package software.amazon.cryptography.materialProviders.model;

import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;

public class VersionBranchKeyInput {
    private final String tableName;

    private final String branchKeyId;

    private final String kmsKeyId;

    private final KmsClient kmsClient;

    private final DynamoDbClient ddbClient;

    protected VersionBranchKeyInput(BuilderImpl builder) {
        this.tableName = builder.tableName();
        this.branchKeyId = builder.branchKeyId();
        this.kmsKeyId = builder.kmsKeyId();
        this.kmsClient = builder.kmsClient();
        this.ddbClient = builder.ddbClient();
    }

    public String tableName() {
        return this.tableName;
    }

    public String branchKeyId() {
        return this.branchKeyId;
    }

    public String kmsKeyId() {
        return this.kmsKeyId;
    }

    public KmsClient kmsClient() {
        return this.kmsClient;
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

        Builder branchKeyId(String branchKeyId);

        String branchKeyId();

        Builder kmsKeyId(String kmsKeyId);

        String kmsKeyId();

        Builder kmsClient(KmsClient kmsClient);

        KmsClient kmsClient();

        Builder ddbClient(DynamoDbClient ddbClient);

        DynamoDbClient ddbClient();

        VersionBranchKeyInput build();
    }

    protected static class BuilderImpl implements Builder {
        protected String tableName;

        protected String branchKeyId;

        protected String kmsKeyId;

        protected KmsClient kmsClient;

        protected DynamoDbClient ddbClient;

        protected BuilderImpl() {
        }

        protected BuilderImpl(VersionBranchKeyInput model) {
            this.tableName = model.tableName();
            this.branchKeyId = model.branchKeyId();
            this.kmsKeyId = model.kmsKeyId();
            this.kmsClient = model.kmsClient();
            this.ddbClient = model.ddbClient();
        }

        public Builder tableName(String tableName) {
            this.tableName = tableName;
            return this;
        }

        public String tableName() {
            return this.tableName;
        }

        public Builder branchKeyId(String branchKeyId) {
            this.branchKeyId = branchKeyId;
            return this;
        }

        public String branchKeyId() {
            return this.branchKeyId;
        }

        public Builder kmsKeyId(String kmsKeyId) {
            this.kmsKeyId = kmsKeyId;
            return this;
        }

        public String kmsKeyId() {
            return this.kmsKeyId;
        }

        public Builder kmsClient(KmsClient kmsClient) {
            this.kmsClient = kmsClient;
            return this;
        }

        public KmsClient kmsClient() {
            return this.kmsClient;
        }

        public Builder ddbClient(DynamoDbClient ddbClient) {
            this.ddbClient = ddbClient;
            return this;
        }

        public DynamoDbClient ddbClient() {
            return this.ddbClient;
        }

        public VersionBranchKeyInput build() {
            return new VersionBranchKeyInput(this);
        }
    }
}