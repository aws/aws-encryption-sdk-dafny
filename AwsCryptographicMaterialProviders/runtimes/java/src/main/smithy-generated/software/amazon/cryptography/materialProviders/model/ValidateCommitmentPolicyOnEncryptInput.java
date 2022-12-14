// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class ValidateCommitmentPolicyOnEncryptInput {
  private final AlgorithmSuiteId algorithm;

  private final CommitmentPolicy commitmentPolicy;

  protected ValidateCommitmentPolicyOnEncryptInput(BuilderImpl builder) {
    this.algorithm = builder.algorithm();
    this.commitmentPolicy = builder.commitmentPolicy();
  }

  public AlgorithmSuiteId algorithm() {
    return this.algorithm;
  }

  public CommitmentPolicy commitmentPolicy() {
    return this.commitmentPolicy;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder algorithm(AlgorithmSuiteId algorithm);

    AlgorithmSuiteId algorithm();

    Builder commitmentPolicy(CommitmentPolicy commitmentPolicy);

    CommitmentPolicy commitmentPolicy();

    ValidateCommitmentPolicyOnEncryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteId algorithm;

    protected CommitmentPolicy commitmentPolicy;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ValidateCommitmentPolicyOnEncryptInput model) {
      this.algorithm = model.algorithm();
      this.commitmentPolicy = model.commitmentPolicy();
    }

    public Builder algorithm(AlgorithmSuiteId algorithm) {
      this.algorithm = algorithm;
      return this;
    }

    public AlgorithmSuiteId algorithm() {
      return this.algorithm;
    }

    public Builder commitmentPolicy(CommitmentPolicy commitmentPolicy) {
      this.commitmentPolicy = commitmentPolicy;
      return this;
    }

    public CommitmentPolicy commitmentPolicy() {
      return this.commitmentPolicy;
    }

    public ValidateCommitmentPolicyOnEncryptInput build() {
      if (Objects.isNull(this.algorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithm`");
      }
      if (Objects.isNull(this.commitmentPolicy()))  {
        throw new IllegalArgumentException("Missing value for required field `commitmentPolicy`");
      }
      return new ValidateCommitmentPolicyOnEncryptInput(this);
    }
  }
}
