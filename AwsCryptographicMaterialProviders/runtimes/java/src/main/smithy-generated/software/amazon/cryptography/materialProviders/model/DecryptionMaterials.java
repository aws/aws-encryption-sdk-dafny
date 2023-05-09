// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class DecryptionMaterials {
  private final AlgorithmSuiteInfo algorithmSuite;

  private final Map<String, String> encryptionContext;

  private final List<String> requiredEncryptionContextKeys;

  private final ByteBuffer plaintextDataKey;

  private final ByteBuffer verificationKey;

  private final ByteBuffer symmetricSigningKey;

  protected DecryptionMaterials(BuilderImpl builder) {
    this.algorithmSuite = builder.algorithmSuite();
    this.encryptionContext = builder.encryptionContext();
    this.requiredEncryptionContextKeys = builder.requiredEncryptionContextKeys();
    this.plaintextDataKey = builder.plaintextDataKey();
    this.verificationKey = builder.verificationKey();
    this.symmetricSigningKey = builder.symmetricSigningKey();
  }

  public AlgorithmSuiteInfo algorithmSuite() {
    return this.algorithmSuite;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public List<String> requiredEncryptionContextKeys() {
    return this.requiredEncryptionContextKeys;
  }

  public ByteBuffer plaintextDataKey() {
    return this.plaintextDataKey;
  }

  public ByteBuffer verificationKey() {
    return this.verificationKey;
  }

  public ByteBuffer symmetricSigningKey() {
    return this.symmetricSigningKey;
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

    Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys);

    List<String> requiredEncryptionContextKeys();

    Builder plaintextDataKey(ByteBuffer plaintextDataKey);

    ByteBuffer plaintextDataKey();

    Builder verificationKey(ByteBuffer verificationKey);

    ByteBuffer verificationKey();

    Builder symmetricSigningKey(ByteBuffer symmetricSigningKey);

    ByteBuffer symmetricSigningKey();

    DecryptionMaterials build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteInfo algorithmSuite;

    protected Map<String, String> encryptionContext;

    protected List<String> requiredEncryptionContextKeys;

    protected ByteBuffer plaintextDataKey;

    protected ByteBuffer verificationKey;

    protected ByteBuffer symmetricSigningKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptionMaterials model) {
      this.algorithmSuite = model.algorithmSuite();
      this.encryptionContext = model.encryptionContext();
      this.requiredEncryptionContextKeys = model.requiredEncryptionContextKeys();
      this.plaintextDataKey = model.plaintextDataKey();
      this.verificationKey = model.verificationKey();
      this.symmetricSigningKey = model.symmetricSigningKey();
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

    public Builder verificationKey(ByteBuffer verificationKey) {
      this.verificationKey = verificationKey;
      return this;
    }

    public ByteBuffer verificationKey() {
      return this.verificationKey;
    }

    public Builder symmetricSigningKey(ByteBuffer symmetricSigningKey) {
      this.symmetricSigningKey = symmetricSigningKey;
      return this;
    }

    public ByteBuffer symmetricSigningKey() {
      return this.symmetricSigningKey;
    }

    public DecryptionMaterials build() {
      if (Objects.isNull(this.algorithmSuite()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuite`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      if (Objects.isNull(this.requiredEncryptionContextKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `requiredEncryptionContextKeys`");
      }
      return new DecryptionMaterials(this);
    }
  }
}
