// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Map;
import java.util.Objects;

public class GetEncryptionMaterialsInput {
  private final Map<String, String> encryptionContext;

  private final CommitmentPolicy commitmentPolicy;

  private final AlgorithmSuiteId algorithmSuiteId;

  private final Long maxPlaintextLength;

  protected GetEncryptionMaterialsInput(BuilderImpl builder) {
    this.encryptionContext = builder.encryptionContext();
    this.commitmentPolicy = builder.commitmentPolicy();
    this.algorithmSuiteId = builder.algorithmSuiteId();
    this.maxPlaintextLength = builder.maxPlaintextLength();
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public CommitmentPolicy commitmentPolicy() {
    return this.commitmentPolicy;
  }

  public AlgorithmSuiteId algorithmSuiteId() {
    return this.algorithmSuiteId;
  }

  public Long maxPlaintextLength() {
    return this.maxPlaintextLength;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder commitmentPolicy(CommitmentPolicy commitmentPolicy);

    CommitmentPolicy commitmentPolicy();

    Builder algorithmSuiteId(AlgorithmSuiteId algorithmSuiteId);

    AlgorithmSuiteId algorithmSuiteId();

    Builder maxPlaintextLength(Long maxPlaintextLength);

    Long maxPlaintextLength();

    GetEncryptionMaterialsInput build();
  }

  static class BuilderImpl implements Builder {
    protected Map<String, String> encryptionContext;

    protected CommitmentPolicy commitmentPolicy;

    protected AlgorithmSuiteId algorithmSuiteId;

    protected Long maxPlaintextLength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetEncryptionMaterialsInput model) {
      this.encryptionContext = model.encryptionContext();
      this.commitmentPolicy = model.commitmentPolicy();
      this.algorithmSuiteId = model.algorithmSuiteId();
      this.maxPlaintextLength = model.maxPlaintextLength();
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder commitmentPolicy(CommitmentPolicy commitmentPolicy) {
      this.commitmentPolicy = commitmentPolicy;
      return this;
    }

    public CommitmentPolicy commitmentPolicy() {
      return this.commitmentPolicy;
    }

    public Builder algorithmSuiteId(AlgorithmSuiteId algorithmSuiteId) {
      this.algorithmSuiteId = algorithmSuiteId;
      return this;
    }

    public AlgorithmSuiteId algorithmSuiteId() {
      return this.algorithmSuiteId;
    }

    public Builder maxPlaintextLength(Long maxPlaintextLength) {
      this.maxPlaintextLength = maxPlaintextLength;
      return this;
    }

    public Long maxPlaintextLength() {
      return this.maxPlaintextLength;
    }

    public GetEncryptionMaterialsInput build() {
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      if (Objects.isNull(this.commitmentPolicy()))  {
        throw new IllegalArgumentException("Missing value for required field `commitmentPolicy`");
      }
      return new GetEncryptionMaterialsInput(this);
    }
  }
}
