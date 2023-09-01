// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.model.ESDKAlgorithmSuiteId;

public class EncryptOutput {
  private final ByteBuffer ciphertext;

  private final Map<String, String> encryptionContext;

  private final ESDKAlgorithmSuiteId algorithmSuiteId;

  protected EncryptOutput(BuilderImpl builder) {
    this.ciphertext = builder.ciphertext();
    this.encryptionContext = builder.encryptionContext();
    this.algorithmSuiteId = builder.algorithmSuiteId();
  }

  public ByteBuffer ciphertext() {
    return this.ciphertext;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public ESDKAlgorithmSuiteId algorithmSuiteId() {
    return this.algorithmSuiteId;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ciphertext(ByteBuffer ciphertext);

    ByteBuffer ciphertext();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder algorithmSuiteId(ESDKAlgorithmSuiteId algorithmSuiteId);

    ESDKAlgorithmSuiteId algorithmSuiteId();

    EncryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer ciphertext;

    protected Map<String, String> encryptionContext;

    protected ESDKAlgorithmSuiteId algorithmSuiteId;

    protected BuilderImpl() {
    }

    protected BuilderImpl(EncryptOutput model) {
      this.ciphertext = model.ciphertext();
      this.encryptionContext = model.encryptionContext();
      this.algorithmSuiteId = model.algorithmSuiteId();
    }

    public Builder ciphertext(ByteBuffer ciphertext) {
      this.ciphertext = ciphertext;
      return this;
    }

    public ByteBuffer ciphertext() {
      return this.ciphertext;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder algorithmSuiteId(ESDKAlgorithmSuiteId algorithmSuiteId) {
      this.algorithmSuiteId = algorithmSuiteId;
      return this;
    }

    public ESDKAlgorithmSuiteId algorithmSuiteId() {
      return this.algorithmSuiteId;
    }

    public EncryptOutput build() {
      if (Objects.isNull(this.ciphertext()))  {
        throw new IllegalArgumentException("Missing value for required field `ciphertext`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      if (Objects.isNull(this.algorithmSuiteId()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuiteId`");
      }
      return new EncryptOutput(this);
    }
  }
}
