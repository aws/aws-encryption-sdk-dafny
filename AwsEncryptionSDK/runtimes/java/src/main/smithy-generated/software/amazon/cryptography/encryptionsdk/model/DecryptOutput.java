// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.model.ESDKAlgorithmSuiteId;

public class DecryptOutput {
  private final ByteBuffer plaintext;

  private final Map<String, String> encryptionContext;

  private final ESDKAlgorithmSuiteId algorithmSuiteId;

  protected DecryptOutput(BuilderImpl builder) {
    this.plaintext = builder.plaintext();
    this.encryptionContext = builder.encryptionContext();
    this.algorithmSuiteId = builder.algorithmSuiteId();
  }

  public ByteBuffer plaintext() {
    return this.plaintext;
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
    Builder plaintext(ByteBuffer plaintext);

    ByteBuffer plaintext();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder algorithmSuiteId(ESDKAlgorithmSuiteId algorithmSuiteId);

    ESDKAlgorithmSuiteId algorithmSuiteId();

    DecryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer plaintext;

    protected Map<String, String> encryptionContext;

    protected ESDKAlgorithmSuiteId algorithmSuiteId;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptOutput model) {
      this.plaintext = model.plaintext();
      this.encryptionContext = model.encryptionContext();
      this.algorithmSuiteId = model.algorithmSuiteId();
    }

    public Builder plaintext(ByteBuffer plaintext) {
      this.plaintext = plaintext;
      return this;
    }

    public ByteBuffer plaintext() {
      return this.plaintext;
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

    public DecryptOutput build() {
      if (Objects.isNull(this.plaintext()))  {
        throw new IllegalArgumentException("Missing value for required field `plaintext`");
      }
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      if (Objects.isNull(this.algorithmSuiteId()))  {
        throw new IllegalArgumentException("Missing value for required field `algorithmSuiteId`");
      }
      return new DecryptOutput(this);
    }
  }
}
