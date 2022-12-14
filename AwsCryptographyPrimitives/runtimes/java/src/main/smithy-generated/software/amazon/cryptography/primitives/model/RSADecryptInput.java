// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSADecryptInput {
  private final RSAPaddingMode padding;

  private final ByteBuffer privateKey;

  private final ByteBuffer cipherText;

  protected RSADecryptInput(BuilderImpl builder) {
    this.padding = builder.padding();
    this.privateKey = builder.privateKey();
    this.cipherText = builder.cipherText();
  }

  public RSAPaddingMode padding() {
    return this.padding;
  }

  public ByteBuffer privateKey() {
    return this.privateKey;
  }

  public ByteBuffer cipherText() {
    return this.cipherText;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder padding(RSAPaddingMode padding);

    RSAPaddingMode padding();

    Builder privateKey(ByteBuffer privateKey);

    ByteBuffer privateKey();

    Builder cipherText(ByteBuffer cipherText);

    ByteBuffer cipherText();

    RSADecryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected RSAPaddingMode padding;

    protected ByteBuffer privateKey;

    protected ByteBuffer cipherText;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSADecryptInput model) {
      this.padding = model.padding();
      this.privateKey = model.privateKey();
      this.cipherText = model.cipherText();
    }

    public Builder padding(RSAPaddingMode padding) {
      this.padding = padding;
      return this;
    }

    public RSAPaddingMode padding() {
      return this.padding;
    }

    public Builder privateKey(ByteBuffer privateKey) {
      this.privateKey = privateKey;
      return this;
    }

    public ByteBuffer privateKey() {
      return this.privateKey;
    }

    public Builder cipherText(ByteBuffer cipherText) {
      this.cipherText = cipherText;
      return this;
    }

    public ByteBuffer cipherText() {
      return this.cipherText;
    }

    public RSADecryptInput build() {
      if (Objects.isNull(this.padding()))  {
        throw new IllegalArgumentException("Missing value for required field `padding`");
      }
      if (Objects.isNull(this.privateKey()))  {
        throw new IllegalArgumentException("Missing value for required field `privateKey`");
      }
      if (Objects.isNull(this.cipherText()))  {
        throw new IllegalArgumentException("Missing value for required field `cipherText`");
      }
      return new RSADecryptInput(this);
    }
  }
}
