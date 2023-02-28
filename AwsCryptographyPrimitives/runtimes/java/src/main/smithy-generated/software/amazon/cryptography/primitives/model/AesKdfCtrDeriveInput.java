// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AesKdfCtrDeriveInput {
  private final ByteBuffer key;

  private final ByteBuffer iv;

  private final int expectedLength;

  protected AesKdfCtrDeriveInput(BuilderImpl builder) {
    this.key = builder.key();
    this.iv = builder.iv();
    this.expectedLength = builder.expectedLength();
  }

  public ByteBuffer key() {
    return this.key;
  }

  public ByteBuffer iv() {
    return this.iv;
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
    Builder key(ByteBuffer key);

    ByteBuffer key();

    Builder iv(ByteBuffer iv);

    ByteBuffer iv();

    Builder expectedLength(int expectedLength);

    int expectedLength();

    AesKdfCtrDeriveInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer key;

    protected ByteBuffer iv;

    protected int expectedLength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AesKdfCtrDeriveInput model) {
      this.key = model.key();
      this.iv = model.iv();
      this.expectedLength = model.expectedLength();
    }

    public Builder key(ByteBuffer key) {
      this.key = key;
      return this;
    }

    public ByteBuffer key() {
      return this.key;
    }

    public Builder iv(ByteBuffer iv) {
      this.iv = iv;
      return this;
    }

    public ByteBuffer iv() {
      return this.iv;
    }

    public Builder expectedLength(int expectedLength) {
      this.expectedLength = expectedLength;
      return this;
    }

    public int expectedLength() {
      return this.expectedLength;
    }

    public AesKdfCtrDeriveInput build() {
      if (Objects.isNull(this.key()))  {
        throw new IllegalArgumentException("Missing value for required field `key`");
      }
      if (Objects.isNull(this.iv()))  {
        throw new IllegalArgumentException("Missing value for required field `iv`");
      }
      if (Objects.isNull(this.expectedLength()))  {
        throw new IllegalArgumentException("Missing value for required field `expectedLength`");
      }
      if (Objects.nonNull(this.expectedLength()) && this.expectedLength() < 0) {
        throw new IllegalArgumentException("`expectedLength` must be greater than or equal to 0");
      }
      return new AesKdfCtrDeriveInput(this);
    }
  }
}
