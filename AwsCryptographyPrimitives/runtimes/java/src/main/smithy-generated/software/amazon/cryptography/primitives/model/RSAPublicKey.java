// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class RSAPublicKey {
  private final int strength;

  private final ByteBuffer pem;

  protected RSAPublicKey(BuilderImpl builder) {
    this.strength = builder.strength();
    this.pem = builder.pem();
  }

  public int strength() {
    return this.strength;
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
    Builder strength(int strength);

    int strength();

    Builder pem(ByteBuffer pem);

    ByteBuffer pem();

    RSAPublicKey build();
  }

  static class BuilderImpl implements Builder {
    protected int strength;

    protected ByteBuffer pem;

    protected BuilderImpl() {
    }

    protected BuilderImpl(RSAPublicKey model) {
      this.strength = model.strength();
      this.pem = model.pem();
    }

    public Builder strength(int strength) {
      this.strength = strength;
      return this;
    }

    public int strength() {
      return this.strength;
    }

    public Builder pem(ByteBuffer pem) {
      this.pem = pem;
      return this;
    }

    public ByteBuffer pem() {
      return this.pem;
    }

    public RSAPublicKey build() {
      if (Objects.isNull(this.strength()))  {
        throw new IllegalArgumentException("Missing value for required field `strength`");
      }
      if (Objects.nonNull(this.strength()) && this.strength() < 81) {
        throw new IllegalArgumentException("`strength` must be greater than or equal to 81");
      }
      if (Objects.nonNull(this.strength()) && this.strength() > 4096) {
        throw new IllegalArgumentException("`strength` must be less than or equal to 4096.");
      }
      if (Objects.isNull(this.pem()))  {
        throw new IllegalArgumentException("Missing value for required field `pem`");
      }
      return new RSAPublicKey(this);
    }
  }
}
