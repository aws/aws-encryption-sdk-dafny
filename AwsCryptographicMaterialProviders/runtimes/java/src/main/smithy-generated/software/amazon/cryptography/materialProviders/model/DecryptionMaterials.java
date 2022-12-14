// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;

public class DecryptionMaterials {
  private final AlgorithmSuiteInfo algorithmSuite;

  private final Map<String, String> encryptionContext;

  private final ByteBuffer plaintextDataKey;

  private final ByteBuffer verificationKey;

  protected DecryptionMaterials(BuilderImpl builder) {
    this.algorithmSuite = builder.algorithmSuite();
    this.encryptionContext = builder.encryptionContext();
    this.plaintextDataKey = builder.plaintextDataKey();
    this.verificationKey = builder.verificationKey();
  }

  public AlgorithmSuiteInfo algorithmSuite() {
    return this.algorithmSuite;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public ByteBuffer plaintextDataKey() {
    return this.plaintextDataKey;
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
    Builder algorithmSuite(AlgorithmSuiteInfo algorithmSuite);

    AlgorithmSuiteInfo algorithmSuite();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder plaintextDataKey(ByteBuffer plaintextDataKey);

    ByteBuffer plaintextDataKey();

    Builder verificationKey(ByteBuffer verificationKey);

    ByteBuffer verificationKey();

    DecryptionMaterials build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteInfo algorithmSuite;

    protected Map<String, String> encryptionContext;

    protected ByteBuffer plaintextDataKey;

    protected ByteBuffer verificationKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptionMaterials model) {
      this.algorithmSuite = model.algorithmSuite();
      this.encryptionContext = model.encryptionContext();
      this.plaintextDataKey = model.plaintextDataKey();
      this.verificationKey = model.verificationKey();
    }

    public Builder algorithmSuite(AlgorithmSuiteInfo algorithmSuite) {
      this.algorithmSuite = algorithmSuite;
      return this;
    }

    public AlgorithmSuiteInfo algorithmSuite() {
      return this.algorithmSuite;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder plaintextDataKey(ByteBuffer plaintextDataKey) {
      this.plaintextDataKey = plaintextDataKey;
      return this;
    }

    public ByteBuffer plaintextDataKey() {
      return this.plaintextDataKey;
    }

    public Builder verificationKey(ByteBuffer verificationKey) {
      this.verificationKey = verificationKey;
      return this;
    }

    public ByteBuffer verificationKey() {
      return this.verificationKey;
    }

    public DecryptionMaterials build() {
      if (Objects.isNull(this.algorithmSuite()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuite`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      return new DecryptionMaterials(this);
    }
  }
}
