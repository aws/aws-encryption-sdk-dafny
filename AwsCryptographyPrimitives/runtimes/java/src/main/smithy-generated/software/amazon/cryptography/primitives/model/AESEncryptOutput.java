// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AESEncryptOutput {
  private final ByteBuffer cipherText;

  private final ByteBuffer authTag;

  protected AESEncryptOutput(BuilderImpl builder) {
    this.cipherText = builder.cipherText();
    this.authTag = builder.authTag();
  }

  public ByteBuffer cipherText() {
    return this.cipherText;
  }

  public ByteBuffer authTag() {
    return this.authTag;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder cipherText(ByteBuffer cipherText);

    ByteBuffer cipherText();

    Builder authTag(ByteBuffer authTag);

    ByteBuffer authTag();

    AESEncryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer cipherText;

    protected ByteBuffer authTag;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AESEncryptOutput model) {
      this.cipherText = model.cipherText();
      this.authTag = model.authTag();
    }

    public Builder cipherText(ByteBuffer cipherText) {
      this.cipherText = cipherText;
      return this;
    }

    public ByteBuffer cipherText() {
      return this.cipherText;
    }

    public Builder authTag(ByteBuffer authTag) {
      this.authTag = authTag;
      return this;
    }

    public ByteBuffer authTag() {
      return this.authTag;
    }

    public AESEncryptOutput build() {
      if (Objects.isNull(this.cipherText()))  {
        throw new IllegalArgumentException("Missing value for required field `cipherText`");
      }
      if (Objects.isNull(this.authTag()))  {
        throw new IllegalArgumentException("Missing value for required field `authTag`");
      }
      return new AESEncryptOutput(this);
    }
  }
}
