// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class EncryptedDataKey {
  private final String keyProviderId;

  private final ByteBuffer keyProviderInfo;

  private final ByteBuffer ciphertext;

  protected EncryptedDataKey(BuilderImpl builder) {
    this.keyProviderId = builder.keyProviderId();
    this.keyProviderInfo = builder.keyProviderInfo();
    this.ciphertext = builder.ciphertext();
  }

  public String keyProviderId() {
    return this.keyProviderId;
  }

  public ByteBuffer keyProviderInfo() {
    return this.keyProviderInfo;
  }

  public ByteBuffer ciphertext() {
    return this.ciphertext;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyProviderId(String keyProviderId);

    String keyProviderId();

    Builder keyProviderInfo(ByteBuffer keyProviderInfo);

    ByteBuffer keyProviderInfo();

    Builder ciphertext(ByteBuffer ciphertext);

    ByteBuffer ciphertext();

    EncryptedDataKey build();
  }

  static class BuilderImpl implements Builder {
    protected String keyProviderId;

    protected ByteBuffer keyProviderInfo;

    protected ByteBuffer ciphertext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(EncryptedDataKey model) {
      this.keyProviderId = model.keyProviderId();
      this.keyProviderInfo = model.keyProviderInfo();
      this.ciphertext = model.ciphertext();
    }

    public Builder keyProviderId(String keyProviderId) {
      this.keyProviderId = keyProviderId;
      return this;
    }

    public String keyProviderId() {
      return this.keyProviderId;
    }

    public Builder keyProviderInfo(ByteBuffer keyProviderInfo) {
      this.keyProviderInfo = keyProviderInfo;
      return this;
    }

    public ByteBuffer keyProviderInfo() {
      return this.keyProviderInfo;
    }

    public Builder ciphertext(ByteBuffer ciphertext) {
      this.ciphertext = ciphertext;
      return this;
    }

    public ByteBuffer ciphertext() {
      return this.ciphertext;
    }

    public EncryptedDataKey build() {
      if (Objects.isNull(this.keyProviderId()))  {
        throw new IllegalArgumentException("Missing value for required field `keyProviderId`");
      }
      if (Objects.isNull(this.keyProviderInfo()))  {
        throw new IllegalArgumentException("Missing value for required field `keyProviderInfo`");
      }
      if (Objects.isNull(this.ciphertext()))  {
        throw new IllegalArgumentException("Missing value for required field `ciphertext`");
      }
      return new EncryptedDataKey(this);
    }
  }
}
