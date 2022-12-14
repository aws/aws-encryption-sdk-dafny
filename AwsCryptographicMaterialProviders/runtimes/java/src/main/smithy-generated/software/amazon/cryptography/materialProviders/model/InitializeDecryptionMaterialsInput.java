// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Map;
import java.util.Objects;

public class InitializeDecryptionMaterialsInput {
  private final AlgorithmSuiteId algorithmSuiteId;

  private final Map<String, String> encryptionContext;

  protected InitializeDecryptionMaterialsInput(BuilderImpl builder) {
    this.algorithmSuiteId = builder.algorithmSuiteId();
    this.encryptionContext = builder.encryptionContext();
  }

  public AlgorithmSuiteId algorithmSuiteId() {
    return this.algorithmSuiteId;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
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

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    InitializeDecryptionMaterialsInput build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteId algorithmSuiteId;

    protected Map<String, String> encryptionContext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(InitializeDecryptionMaterialsInput model) {
      this.algorithmSuiteId = model.algorithmSuiteId();
      this.encryptionContext = model.encryptionContext();
    }

    public Builder algorithmSuiteId(AlgorithmSuiteId algorithmSuiteId) {
      this.algorithmSuiteId = algorithmSuiteId;
      return this;
    }

    public AlgorithmSuiteId algorithmSuiteId() {
      return this.algorithmSuiteId;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public InitializeDecryptionMaterialsInput build() {
      if (Objects.isNull(this.algorithmSuiteId()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuiteId`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      return new InitializeDecryptionMaterialsInput(this);
    }
  }
}
