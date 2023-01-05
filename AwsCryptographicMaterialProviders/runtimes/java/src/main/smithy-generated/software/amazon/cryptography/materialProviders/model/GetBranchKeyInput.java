package software.amazon.cryptography.materialProviders.model;

import java.util.Map;

public class GetBranchKeyInput {
    private final Map<String, String> context;

    protected GetBranchKeyInput(BuilderImpl builder) {
        this.context = builder.context();
    }

    public Map<String, String> context() {
        return this.context;
    }

    public Builder toBuilder() {
        return new BuilderImpl(this);
    }

    public static Builder builder() {
        return new BuilderImpl();
    }

    public interface Builder {
        Builder context(Map<String, String> context);

        Map<String, String> context();

        GetBranchKeyInput build();
    }

    protected static class BuilderImpl implements Builder {
        protected Map<String, String> context;

        protected BuilderImpl() {
        }

        protected BuilderImpl(GetBranchKeyInput model) {
            this.context = model.context();
        }

        public Builder context(Map<String, String> context) {
            this.context = context;
            return this;
        }

        public Map<String, String> context() {
            return this.context;
        }

        public GetBranchKeyInput build() {
            return new GetBranchKeyInput(this);
        }
    }
}