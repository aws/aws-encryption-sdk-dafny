// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class EncryptionMaterials {
  private final AlgorithmSuiteInfo algorithmSuite;

  private final Map<String, String> encryptionContext;

  private final List<EncryptedDataKey> encryptedDataKeys;

  private final List<String> requiredEncryptionContextKeys;

  private final ByteBuffer plaintextDataKey;

  private final ByteBuffer signingKey;

  private final List<ByteBuffer> symmetricSigningKeys;

  protected EncryptionMaterials(BuilderImpl builder) {
    this.algorithmSuite = builder.algorithmSuite();
    this.encryptionContext = builder.encryptionContext();
    this.encryptedDataKeys = builder.encryptedDataKeys();
    this.requiredEncryptionContextKeys = builder.requiredEncryptionContextKeys();
    this.plaintextDataKey = builder.plaintextDataKey();
    this.signingKey = builder.signingKey();
    this.symmetricSigningKeys = builder.symmetricSigningKeys();
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

  public List<String> requiredEncryptionContextKeys() {
    return this.requiredEncryptionContextKeys;
  }

  public ByteBuffer plaintextDataKey() {
    return this.plaintextDataKey;
  }

  public ByteBuffer signingKey() {
    return this.signingKey;
  }

  public List<ByteBuffer> symmetricSigningKeys() {
    return this.symmetricSigningKeys;
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

    Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys);

    List<String> requiredEncryptionContextKeys();

    Builder plaintextDataKey(ByteBuffer plaintextDataKey);

    ByteBuffer plaintextDataKey();

    Builder signingKey(ByteBuffer signingKey);

    ByteBuffer signingKey();

    Builder symmetricSigningKeys(List<ByteBuffer> symmetricSigningKeys);

    List<ByteBuffer> symmetricSigningKeys();

    EncryptionMaterials build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteInfo algorithmSuite;

    protected Map<String, String> encryptionContext;

    protected List<EncryptedDataKey> encryptedDataKeys;

    protected List<String> requiredEncryptionContextKeys;

    protected ByteBuffer plaintextDataKey;

    protected ByteBuffer signingKey;

    protected List<ByteBuffer> symmetricSigningKeys;

    protected BuilderImpl() {
    }

    protected BuilderImpl(EncryptionMaterials model) {
      this.algorithmSuite = model.algorithmSuite();
      this.encryptionContext = model.encryptionContext();
      this.encryptedDataKeys = model.encryptedDataKeys();
      this.requiredEncryptionContextKeys = model.requiredEncryptionContextKeys();
      this.plaintextDataKey = model.plaintextDataKey();
      this.signingKey = model.signingKey();
      this.symmetricSigningKeys = model.symmetricSigningKeys();
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

    public Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys) {
      this.requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      return this;
    }

    public List<String> requiredEncryptionContextKeys() {
      return this.requiredEncryptionContextKeys;
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

    public Builder symmetricSigningKeys(List<ByteBuffer> symmetricSigningKeys) {
      this.symmetricSigningKeys = symmetricSigningKeys;
      return this;
    }

    public List<ByteBuffer> symmetricSigningKeys() {
      return this.symmetricSigningKeys;
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
      if (Objects.isNull(this.requiredEncryptionContextKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `requiredEncryptionContextKeys`");
      }
      return new EncryptionMaterials(this);
    }
  }
}
