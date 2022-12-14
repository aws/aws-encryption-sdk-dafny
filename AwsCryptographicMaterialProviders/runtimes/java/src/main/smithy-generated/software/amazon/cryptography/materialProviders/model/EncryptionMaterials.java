// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class EncryptionMaterials {
  private final AlgorithmSuiteInfo algorithmSuite;

  private final Map<String, String> encryptionContext;

  private final List<EncryptedDataKey> encryptedDataKeys;

  private final ByteBuffer plaintextDataKey;

  private final ByteBuffer signingKey;

  protected EncryptionMaterials(BuilderImpl builder) {
    this.algorithmSuite = builder.algorithmSuite();
    this.encryptionContext = builder.encryptionContext();
    this.encryptedDataKeys = builder.encryptedDataKeys();
    this.plaintextDataKey = builder.plaintextDataKey();
    this.signingKey = builder.signingKey();
  }

  public AlgorithmSuiteInfo algorithmSuite() {
    return this.algorithmSuite;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public List<EncryptedDataKey> encryptedDataKeys() {
    return this.encryptedDataKeys;
  }

  public ByteBuffer plaintextDataKey() {
    return this.plaintextDataKey;
  }

  public ByteBuffer signingKey() {
    return this.signingKey;
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

    Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys);

    List<EncryptedDataKey> encryptedDataKeys();

    Builder plaintextDataKey(ByteBuffer plaintextDataKey);

    ByteBuffer plaintextDataKey();

    Builder signingKey(ByteBuffer signingKey);

    ByteBuffer signingKey();

    EncryptionMaterials build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteInfo algorithmSuite;

    protected Map<String, String> encryptionContext;

    protected List<EncryptedDataKey> encryptedDataKeys;

    protected ByteBuffer plaintextDataKey;

    protected ByteBuffer signingKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(EncryptionMaterials model) {
      this.algorithmSuite = model.algorithmSuite();
      this.encryptionContext = model.encryptionContext();
      this.encryptedDataKeys = model.encryptedDataKeys();
      this.plaintextDataKey = model.plaintextDataKey();
      this.signingKey = model.signingKey();
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

    public Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys) {
      this.encryptedDataKeys = encryptedDataKeys;
      return this;
    }

    public List<EncryptedDataKey> encryptedDataKeys() {
      return this.encryptedDataKeys;
    }

    public Builder plaintextDataKey(ByteBuffer plaintextDataKey) {
      this.plaintextDataKey = plaintextDataKey;
      return this;
    }

    public ByteBuffer plaintextDataKey() {
      return this.plaintextDataKey;
    }

    public Builder signingKey(ByteBuffer signingKey) {
      this.signingKey = signingKey;
      return this;
    }

    public ByteBuffer signingKey() {
      return this.signingKey;
    }

    public EncryptionMaterials build() {
      if (Objects.isNull(this.algorithmSuite()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuite`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      if (Objects.isNull(this.encryptedDataKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptedDataKeys`");
      }
      return new EncryptionMaterials(this);
    }
  }
}
