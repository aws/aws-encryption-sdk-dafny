package software.amazon.cryptography.materialProviders.model;

import java.util.Map;
import software.amazon.awssdk.services.dynamodb.model.AttributeValue;

public class GetBranchKeyFromItemInput {
    private final Map<String, AttributeValue> item;

    protected GetBranchKeyFromItemInput(BuilderImpl builder) {
        this.item = builder.item();
    }

    public Map<String, AttributeValue> item() {
        return this.item;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder item(Map<String, AttributeValue> item);

        Map<String, AttributeValue> item();

        GetBranchKeyFromItemInput build();
    }

    protected static class BuilderImpl implements Builder {
        protected Map<String, AttributeValue> item;

        protected BuilderImpl() {
        }

        protected BuilderImpl(GetBranchKeyFromItemInput model) {
            this.item = model.item();
        }

        public Builder item(Map<String, AttributeValue> item) {
            this.item = item;
            return this;
        }

        public Map<String, AttributeValue> item() {
            return this.item;
        }

        public GetBranchKeyFromItemInput build() {
            return new GetBranchKeyFromItemInput(this);
        }
    }
}