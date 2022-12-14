// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;

public class InitializeEncryptionMaterialsInput {
  private final AlgorithmSuiteId algorithmSuiteId;

  private final Map<String, String> encryptionContext;

  private final ByteBuffer signingKey;

  private final ByteBuffer verificationKey;

  protected InitializeEncryptionMaterialsInput(BuilderImpl builder) {
    this.algorithmSuiteId = builder.algorithmSuiteId();
    this.encryptionContext = builder.encryptionContext();
    this.signingKey = builder.signingKey();
    this.verificationKey = builder.verificationKey();
  }

  public AlgorithmSuiteId algorithmSuiteId() {
    return this.algorithmSuiteId;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public ByteBuffer signingKey() {
    return this.signingKey;
  }

  public ByteBuffer verificationKey() {
    return this.verificationKey;
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

    Builder signingKey(ByteBuffer signingKey);

    ByteBuffer signingKey();

    Builder verificationKey(ByteBuffer verificationKey);

    ByteBuffer verificationKey();

    InitializeEncryptionMaterialsInput build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteId algorithmSuiteId;

    protected Map<String, String> encryptionContext;

    protected ByteBuffer signingKey;

    protected ByteBuffer verificationKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(InitializeEncryptionMaterialsInput model) {
      this.algorithmSuiteId = model.algorithmSuiteId();
      this.encryptionContext = model.encryptionContext();
      this.signingKey = model.signingKey();
      this.verificationKey = model.verificationKey();
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

    public Builder signingKey(ByteBuffer signingKey) {
      this.signingKey = signingKey;
      return this;
    }

    public ByteBuffer signingKey() {
      return this.signingKey;
    }

    public Builder verificationKey(ByteBuffer verificationKey) {
      this.verificationKey = verificationKey;
      return this;
    }

    public ByteBuffer verificationKey() {
      return this.verificationKey;
    }

    public InitializeEncryptionMaterialsInput build() {
      if (Objects.isNull(this.algorithmSuiteId()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuiteId`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      return new InitializeEncryptionMaterialsInput(this);
    }
  }
}
