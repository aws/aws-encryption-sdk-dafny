// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

public class AES_GCM {
  private final int keyLength;

  private final int tagLength;

  private final int ivLength;

  protected AES_GCM(BuilderImpl builder) {
    this.keyLength = builder.keyLength();
    this.tagLength = builder.tagLength();
    this.ivLength = builder.ivLength();
  }

  public int keyLength() {
    return this.keyLength;
  }

  public int tagLength() {
    return this.tagLength;
  }

  public int ivLength() {
    return this.ivLength;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyLength(int keyLength);

    int keyLength();

    Builder tagLength(int tagLength);

    int tagLength();

    Builder ivLength(int ivLength);

    int ivLength();

    AES_GCM build();
  }

  static class BuilderImpl implements Builder {
    protected int keyLength;

    private boolean _keyLengthSet = false;

    protected int tagLength;

    private boolean _tagLengthSet = false;

    protected int ivLength;

    private boolean _ivLengthSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AES_GCM model) {
      this.keyLength = model.keyLength();
      this._keyLengthSet = true;
      this.tagLength = model.tagLength();
      this._tagLengthSet = true;
      this.ivLength = model.ivLength();
      this._ivLengthSet = true;
    }

    public Builder keyLength(int keyLength) {
      this.keyLength = keyLength;
      this._keyLengthSet = true;
      return this;
    }

    public int keyLength() {
      return this.keyLength;
    }

    public Builder tagLength(int tagLength) {
      this.tagLength = tagLength;
      this._tagLengthSet = true;
      return this;
    }

    public int tagLength() {
      return this.tagLength;
    }

    public Builder ivLength(int ivLength) {
      this.ivLength = ivLength;
      this._ivLengthSet = true;
      return this;
    }

    public int ivLength() {
      return this.ivLength;
    }

    public AES_GCM build() {
      if (!this._keyLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `keyLength`");
      }
      if (this._keyLengthSet && this.keyLength() < 1) {
        throw new IllegalArgumentException("`keyLength` must be greater than or equal to 1");
      }
      if (this._keyLengthSet && this.keyLength() > 32) {
        throw new IllegalArgumentException("`keyLength` must be less than or equal to 32.");
      }
      if (!this._tagLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `tagLength`");
      }
      if (this._tagLengthSet && this.tagLength() < 0) {
        throw new IllegalArgumentException("`tagLength` must be greater than or equal to 0");
      }
      if (this._tagLengthSet && this.tagLength() > 32) {
        throw new IllegalArgumentException("`tagLength` must be less than or equal to 32.");
      }
      if (!this._ivLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `ivLength`");
      }
      if (this._ivLengthSet && this.ivLength() < 0) {
        throw new IllegalArgumentException("`ivLength` must be greater than or equal to 0");
      }
      if (this._ivLengthSet && this.ivLength() > 255) {
        throw new IllegalArgumentException("`ivLength` must be less than or equal to 255.");
      }
      return new AES_GCM(this);
    }
  }
}
