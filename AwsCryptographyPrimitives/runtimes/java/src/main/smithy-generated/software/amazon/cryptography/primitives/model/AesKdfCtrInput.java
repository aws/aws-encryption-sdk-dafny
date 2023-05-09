// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AesKdfCtrInput {
  private final ByteBuffer ikm;

  private final int expectedLength;

  private final ByteBuffer nonce;

  protected AesKdfCtrInput(BuilderImpl builder) {
    this.ikm = builder.ikm();
    this.expectedLength = builder.expectedLength();
    this.nonce = builder.nonce();
  }

  public ByteBuffer ikm() {
    return this.ikm;
  }

  public int expectedLength() {
    return this.expectedLength;
  }

  public ByteBuffer nonce() {
    return this.nonce;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ikm(ByteBuffer ikm);

    ByteBuffer ikm();

    Builder expectedLength(int expectedLength);

    int expectedLength();

    Builder nonce(ByteBuffer nonce);

    ByteBuffer nonce();

    AesKdfCtrInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer ikm;

    protected int expectedLength;

    private boolean _expectedLengthSet = false;

    protected ByteBuffer nonce;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AesKdfCtrInput model) {
      this.ikm = model.ikm();
      this.expectedLength = model.expectedLength();
      this._expectedLengthSet = true;
      this.nonce = model.nonce();
    }

    public Builder ikm(ByteBuffer ikm) {
      this.ikm = ikm;
      return this;
    }

    public ByteBuffer ikm() {
      return this.ikm;
    }

    public Builder expectedLength(int expectedLength) {
      this.expectedLength = expectedLength;
      this._expectedLengthSet = true;
      return this;
    }

    public int expectedLength() {
      return this.expectedLength;
    }

    public Builder nonce(ByteBuffer nonce) {
      this.nonce = nonce;
      return this;
    }

    public ByteBuffer nonce() {
      return this.nonce;
    }

    public AesKdfCtrInput build() {
      if (Objects.isNull(this.ikm()))  {
        throw new IllegalArgumentException("Missing value for required field `ikm`");
      }
      if (!this._expectedLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `expectedLength`");
      }
      if (this._expectedLengthSet && this.expectedLength() < 0) {
        throw new IllegalArgumentException("`expectedLength` must be greater than or equal to 0");
      }
      return new AesKdfCtrInput(this);
    }
  }
}
