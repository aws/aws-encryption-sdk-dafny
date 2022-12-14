// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

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

    protected int tagLength;

    protected int ivLength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AES_GCM model) {
      this.keyLength = model.keyLength();
      this.tagLength = model.tagLength();
      this.ivLength = model.ivLength();
    }

    public Builder keyLength(int keyLength) {
      this.keyLength = keyLength;
      return this;
    }

    public int keyLength() {
      return this.keyLength;
    }

    public Builder tagLength(int tagLength) {
      this.tagLength = tagLength;
      return this;
    }

    public int tagLength() {
      return this.tagLength;
    }

    public Builder ivLength(int ivLength) {
      this.ivLength = ivLength;
      return this;
    }

    public int ivLength() {
      return this.ivLength;
    }

    public AES_GCM build() {
      if (Objects.isNull(this.keyLength()))  {
        throw new IllegalArgumentException("Missing value for required field `keyLength`");
      }
      if (Objects.nonNull(this.keyLength()) && this.keyLength() < 1) {
        throw new IllegalArgumentException("`keyLength` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.keyLength()) && this.keyLength() > 32) {
        throw new IllegalArgumentException("`keyLength` must be less than or equal to 32.");
      }
      if (Objects.isNull(this.tagLength()))  {
        throw new IllegalArgumentException("Missing value for required field `tagLength`");
      }
      if (Objects.nonNull(this.tagLength()) && this.tagLength() < 0) {
        throw new IllegalArgumentException("`tagLength` must be greater than or equal to 0");
      }
      if (Objects.nonNull(this.tagLength()) && this.tagLength() > 32) {
        throw new IllegalArgumentException("`tagLength` must be less than or equal to 32.");
      }
      if (Objects.isNull(this.ivLength()))  {
        throw new IllegalArgumentException("Missing value for required field `ivLength`");
      }
      if (Objects.nonNull(this.ivLength()) && this.ivLength() < 0) {
        throw new IllegalArgumentException("`ivLength` must be greater than or equal to 0");
      }
      if (Objects.nonNull(this.ivLength()) && this.ivLength() > 255) {
        throw new IllegalArgumentException("`ivLength` must be less than or equal to 255.");
      }
      return new AES_GCM(this);
    }
  }
}
