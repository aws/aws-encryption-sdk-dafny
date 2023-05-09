// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class KdfCtrInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer ikm;

  private final int expectedLength;

  private final ByteBuffer purpose;

  private final ByteBuffer nonce;

  protected KdfCtrInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.ikm = builder.ikm();
    this.expectedLength = builder.expectedLength();
    this.purpose = builder.purpose();
    this.nonce = builder.nonce();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer ikm() {
    return this.ikm;
  }

  public int expectedLength() {
    return this.expectedLength;
  }

  public ByteBuffer purpose() {
    return this.purpose;
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
    Builder digestAlgorithm(DigestAlgorithm digestAlgorithm);

    DigestAlgorithm digestAlgorithm();

    Builder ikm(ByteBuffer ikm);

    ByteBuffer ikm();

    Builder expectedLength(int expectedLength);

    int expectedLength();

    Builder purpose(ByteBuffer purpose);

    ByteBuffer purpose();

    Builder nonce(ByteBuffer nonce);

    ByteBuffer nonce();

    KdfCtrInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer ikm;

    protected int expectedLength;

    private boolean _expectedLengthSet = false;

    protected ByteBuffer purpose;

    protected ByteBuffer nonce;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KdfCtrInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.ikm = model.ikm();
      this.expectedLength = model.expectedLength();
      this._expectedLengthSet = true;
      this.purpose = model.purpose();
      this.nonce = model.nonce();
    }

    public Builder digestAlgorithm(DigestAlgorithm digestAlgorithm) {
      this.digestAlgorithm = digestAlgorithm;
      return this;
    }

    public DigestAlgorithm digestAlgorithm() {
      return this.digestAlgorithm;
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

    public Builder purpose(ByteBuffer purpose) {
      this.purpose = purpose;
      return this;
    }

    public ByteBuffer purpose() {
      return this.purpose;
    }

    public Builder nonce(ByteBuffer nonce) {
      this.nonce = nonce;
      return this;
    }

    public ByteBuffer nonce() {
      return this.nonce;
    }

    public KdfCtrInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.ikm()))  {
        throw new IllegalArgumentException("Missing value for required field `ikm`");
      }
      if (!this._expectedLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `expectedLength`");
      }
      if (this._expectedLengthSet && this.expectedLength() < 0) {
        throw new IllegalArgumentException("`expectedLength` must be greater than or equal to 0");
      }
      return new KdfCtrInput(this);
    }
  }
}
