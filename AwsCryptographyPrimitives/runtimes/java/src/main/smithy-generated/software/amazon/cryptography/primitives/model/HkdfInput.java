// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class HkdfInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer salt;

  private final ByteBuffer ikm;

  private final ByteBuffer info;

  private final int expectedLength;

  protected HkdfInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.salt = builder.salt();
    this.ikm = builder.ikm();
    this.info = builder.info();
    this.expectedLength = builder.expectedLength();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer salt() {
    return this.salt;
  }

  public ByteBuffer ikm() {
    return this.ikm;
  }

  public ByteBuffer info() {
    return this.info;
  }

  public int expectedLength() {
    return this.expectedLength;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder digestAlgorithm(DigestAlgorithm digestAlgorithm);

    DigestAlgorithm digestAlgorithm();

    Builder salt(ByteBuffer salt);

    ByteBuffer salt();

    Builder ikm(ByteBuffer ikm);

    ByteBuffer ikm();

    Builder info(ByteBuffer info);

    ByteBuffer info();

    Builder expectedLength(int expectedLength);

    int expectedLength();

    HkdfInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer salt;

    protected ByteBuffer ikm;

    protected ByteBuffer info;

    protected int expectedLength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HkdfInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.salt = model.salt();
      this.ikm = model.ikm();
      this.info = model.info();
      this.expectedLength = model.expectedLength();
    }

    public Builder digestAlgorithm(DigestAlgorithm digestAlgorithm) {
      this.digestAlgorithm = digestAlgorithm;
      return this;
    }

    public DigestAlgorithm digestAlgorithm() {
      return this.digestAlgorithm;
    }

    public Builder salt(ByteBuffer salt) {
      this.salt = salt;
      return this;
    }

    public ByteBuffer salt() {
      return this.salt;
    }

    public Builder ikm(ByteBuffer ikm) {
      this.ikm = ikm;
      return this;
    }

    public ByteBuffer ikm() {
      return this.ikm;
    }

    public Builder info(ByteBuffer info) {
      this.info = info;
      return this;
    }

    public ByteBuffer info() {
      return this.info;
    }

    public Builder expectedLength(int expectedLength) {
      this.expectedLength = expectedLength;
      return this;
    }

    public int expectedLength() {
      return this.expectedLength;
    }

    public HkdfInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.ikm()))  {
        throw new IllegalArgumentException("Missing value for required field `ikm`");
      }
      if (Objects.isNull(this.info()))  {
        throw new IllegalArgumentException("Missing value for required field `info`");
      }
      if (Objects.isNull(this.expectedLength()))  {
        throw new IllegalArgumentException("Missing value for required field `expectedLength`");
      }
      if (Objects.nonNull(this.expectedLength()) && this.expectedLength() < 0) {
        throw new IllegalArgumentException("`expectedLength` must be greater than or equal to 0");
      }
      return new HkdfInput(this);
    }
  }
}
