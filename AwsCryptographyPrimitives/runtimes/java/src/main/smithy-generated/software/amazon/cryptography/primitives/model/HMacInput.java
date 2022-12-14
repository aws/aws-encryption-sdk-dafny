// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class HMacInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer key;

  private final ByteBuffer message;

  protected HMacInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.key = builder.key();
    this.message = builder.message();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer key() {
    return this.key;
  }

  public ByteBuffer message() {
    return this.message;
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

    Builder key(ByteBuffer key);

    ByteBuffer key();

    Builder message(ByteBuffer message);

    ByteBuffer message();

    HMacInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer key;

    protected ByteBuffer message;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HMacInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.key = model.key();
      this.message = model.message();
    }

    public Builder digestAlgorithm(DigestAlgorithm digestAlgorithm) {
      this.digestAlgorithm = digestAlgorithm;
      return this;
    }

    public DigestAlgorithm digestAlgorithm() {
      return this.digestAlgorithm;
    }

    public Builder key(ByteBuffer key) {
      this.key = key;
      return this;
    }

    public ByteBuffer key() {
      return this.key;
    }

    public Builder message(ByteBuffer message) {
      this.message = message;
      return this;
    }

    public ByteBuffer message() {
      return this.message;
    }

    public HMacInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.key()))  {
        throw new IllegalArgumentException("Missing value for required field `key`");
      }
      if (Objects.isNull(this.message()))  {
        throw new IllegalArgumentException("Missing value for required field `message`");
      }
      return new HMacInput(this);
    }
  }
}
