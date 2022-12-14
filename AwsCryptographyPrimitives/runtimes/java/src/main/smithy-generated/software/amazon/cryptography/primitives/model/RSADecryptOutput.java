// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSADecryptOutput {
  private final ByteBuffer plaintext;

  protected RSADecryptOutput(BuilderImpl builder) {
    this.plaintext = builder.plaintext();
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
    Builder plaintext(ByteBuffer plaintext);

    ByteBuffer plaintext();

    RSADecryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer plaintext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSADecryptOutput model) {
      this.plaintext = model.plaintext();
    }

    public Builder plaintext(ByteBuffer plaintext) {
      this.plaintext = plaintext;
      return this;
    }

    public ByteBuffer plaintext() {
      return this.plaintext;
    }

    public RSADecryptOutput build() {
      if (Objects.isNull(this.plaintext()))  {
        throw new IllegalArgumentException("Missing value for required field `plaintext`");
      }
      return new RSADecryptOutput(this);
    }
  }
}
