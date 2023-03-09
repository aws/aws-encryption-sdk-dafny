// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Map;
import java.util.Objects;

public class DecryptMaterialsInput {
  private final AlgorithmSuiteId algorithmSuiteId;

  private final CommitmentPolicy commitmentPolicy;

  private final List<EncryptedDataKey> encryptedDataKeys;

  private final Map<String, String> encryptionContext;

  private final Map<String, String> reproducedEncryptionContext;

  protected DecryptMaterialsInput(BuilderImpl builder) {
    this.algorithmSuiteId = builder.algorithmSuiteId();
    this.commitmentPolicy = builder.commitmentPolicy();
    this.encryptedDataKeys = builder.encryptedDataKeys();
    this.encryptionContext = builder.encryptionContext();
    this.reproducedEncryptionContext = builder.reproducedEncryptionContext();
  }

  public AlgorithmSuiteId algorithmSuiteId() {
    return this.algorithmSuiteId;
  }

  public CommitmentPolicy commitmentPolicy() {
    return this.commitmentPolicy;
  }

  public List<EncryptedDataKey> encryptedDataKeys() {
    return this.encryptedDataKeys;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public Map<String, String> reproducedEncryptionContext() {
    return this.reproducedEncryptionContext;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder algorithmSuiteId(AlgorithmSuiteId algorithmSuiteId);

    AlgorithmSuiteId algorithmSuiteId();

    Builder commitmentPolicy(CommitmentPolicy commitmentPolicy);

    CommitmentPolicy commitmentPolicy();

    Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys);

    List<EncryptedDataKey> encryptedDataKeys();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder reproducedEncryptionContext(Map<String, String> reproducedEncryptionContext);

    Map<String, String> reproducedEncryptionContext();

    DecryptMaterialsInput build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteId algorithmSuiteId;

    protected CommitmentPolicy commitmentPolicy;

    protected List<EncryptedDataKey> encryptedDataKeys;

    protected Map<String, String> encryptionContext;

    protected Map<String, String> reproducedEncryptionContext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptMaterialsInput model) {
      this.algorithmSuiteId = model.algorithmSuiteId();
      this.commitmentPolicy = model.commitmentPolicy();
      this.encryptedDataKeys = model.encryptedDataKeys();
      this.encryptionContext = model.encryptionContext();
      this.reproducedEncryptionContext = model.reproducedEncryptionContext();
    }

    public Builder algorithmSuiteId(AlgorithmSuiteId algorithmSuiteId) {
      this.algorithmSuiteId = algorithmSuiteId;
      return this;
    }

    public AlgorithmSuiteId algorithmSuiteId() {
      return this.algorithmSuiteId;
    }

    public Builder commitmentPolicy(CommitmentPolicy commitmentPolicy) {
      this.commitmentPolicy = commitmentPolicy;
      return this;
    }

    public CommitmentPolicy commitmentPolicy() {
      return this.commitmentPolicy;
    }

    public Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys) {
      this.encryptedDataKeys = encryptedDataKeys;
      return this;
    }

    public List<EncryptedDataKey> encryptedDataKeys() {
      return this.encryptedDataKeys;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder reproducedEncryptionContext(Map<String, String> reproducedEncryptionContext) {
      this.reproducedEncryptionContext = reproducedEncryptionContext;
      return this;
    }

    public Map<String, String> reproducedEncryptionContext() {
      return this.reproducedEncryptionContext;
    }

    public DecryptMaterialsInput build() {
      if (Objects.isNull(this.algorithmSuiteId()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuiteId`");
      }
      if (Objects.isNull(this.commitmentPolicy()))  {
        throw new IllegalArgumentException("Missing value for required field `commitmentPolicy`");
      }
      if (Objects.isNull(this.encryptedDataKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptedDataKeys`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      return new DecryptMaterialsInput(this);
    }
  }
}
