// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSAEncryptInput {
  private final RSAPaddingMode padding;

  private final ByteBuffer publicKey;

  private final ByteBuffer plaintext;

  protected RSAEncryptInput(BuilderImpl builder) {
    this.padding = builder.padding();
    this.publicKey = builder.publicKey();
    this.plaintext = builder.plaintext();
  }

  public RSAPaddingMode padding() {
    return this.padding;
  }

  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  public ByteBuffer plaintext() {
    return this.plaintext;
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

    Builder publicKey(ByteBuffer publicKey);

    ByteBuffer publicKey();

    Builder plaintext(ByteBuffer plaintext);

    ByteBuffer plaintext();

    RSAEncryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected RSAPaddingMode padding;

    protected ByteBuffer publicKey;

    protected ByteBuffer plaintext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSAEncryptInput model) {
      this.padding = model.padding();
      this.publicKey = model.publicKey();
      this.plaintext = model.plaintext();
    }

    public Builder padding(RSAPaddingMode padding) {
      this.padding = padding;
      return this;
    }

    public RSAPaddingMode padding() {
      return this.padding;
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public Builder plaintext(ByteBuffer plaintext) {
      this.plaintext = plaintext;
      return this;
    }

    public ByteBuffer plaintext() {
      return this.plaintext;
    }

    public RSAEncryptInput build() {
      if (Objects.isNull(this.padding()))  {
        throw new IllegalArgumentException("Missing value for required field `padding`");
      }
      if (Objects.isNull(this.publicKey()))  {
        throw new IllegalArgumentException("Missing value for required field `publicKey`");
      }
      if (Objects.isNull(this.plaintext()))  {
        throw new IllegalArgumentException("Missing value for required field `plaintext`");
      }
      return new RSAEncryptInput(this);
    }
  }
}
