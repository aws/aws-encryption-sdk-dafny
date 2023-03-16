// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSAPublicKey {
  private final int lengthBits;

  private final ByteBuffer pem;

  protected RSAPublicKey(BuilderImpl builder) {
    this.lengthBits = builder.lengthBits();
    this.pem = builder.pem();
  }

  public int lengthBits() {
    return this.lengthBits;
  }

  public ByteBuffer pem() {
    return this.pem;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder lengthBits(int lengthBits);

    int lengthBits();

    Builder pem(ByteBuffer pem);

    ByteBuffer pem();

    RSAPublicKey build();
  }

  static class BuilderImpl implements Builder {
    protected int lengthBits;

    protected ByteBuffer pem;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSAPublicKey model) {
      this.lengthBits = model.lengthBits();
      this.pem = model.pem();
    }

    public Builder lengthBits(int lengthBits) {
      this.lengthBits = lengthBits;
      return this;
    }

    public int lengthBits() {
      return this.lengthBits;
    }

    public Builder pem(ByteBuffer pem) {
      this.pem = pem;
      return this;
    }

    public ByteBuffer pem() {
      return this.pem;
    }

    public RSAPublicKey build() {
      if (Objects.isNull(this.lengthBits()))  {
        throw new IllegalArgumentException("Missing value for required field `lengthBits`");
      }
      if (Objects.nonNull(this.lengthBits()) && this.lengthBits() < 81) {
        throw new IllegalArgumentException("`lengthBits` must be greater than or equal to 81");
      }
      if (Objects.isNull(this.pem()))  {
        throw new IllegalArgumentException("Missing value for required field `pem`");
      }
      return new RSAPublicKey(this);
    }
  }
}
