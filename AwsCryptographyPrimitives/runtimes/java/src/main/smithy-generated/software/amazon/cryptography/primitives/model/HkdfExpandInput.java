// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class HkdfExpandInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer prk;

  private final ByteBuffer info;

  private final int expectedLength;

  protected HkdfExpandInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.prk = builder.prk();
    this.info = builder.info();
    this.expectedLength = builder.expectedLength();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer prk() {
    return this.prk;
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

    Builder prk(ByteBuffer prk);

    ByteBuffer prk();

    Builder info(ByteBuffer info);

    ByteBuffer info();

    Builder expectedLength(int expectedLength);

    int expectedLength();

    HkdfExpandInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer prk;

    protected ByteBuffer info;

    protected int expectedLength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HkdfExpandInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.prk = model.prk();
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

    public Builder prk(ByteBuffer prk) {
      this.prk = prk;
      return this;
    }

    public ByteBuffer prk() {
      return this.prk;
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

    public HkdfExpandInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.prk()))  {
        throw new IllegalArgumentException("Missing value for required field `prk`");
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
      return new HkdfExpandInput(this);
    }
  }
}
