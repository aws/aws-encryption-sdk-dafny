// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSAEncryptOutput {
  private final ByteBuffer cipherText;

  protected RSAEncryptOutput(BuilderImpl builder) {
    this.cipherText = builder.cipherText();
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
    Builder cipherText(ByteBuffer cipherText);

    ByteBuffer cipherText();

    RSAEncryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer cipherText;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSAEncryptOutput model) {
      this.cipherText = model.cipherText();
    }

    public Builder cipherText(ByteBuffer cipherText) {
      this.cipherText = cipherText;
      return this;
    }

    public ByteBuffer cipherText() {
      return this.cipherText;
    }

    public RSAEncryptOutput build() {
      if (Objects.isNull(this.cipherText()))  {
        throw new IllegalArgumentException("Missing value for required field `cipherText`");
      }
      return new RSAEncryptOutput(this);
    }
  }
}
