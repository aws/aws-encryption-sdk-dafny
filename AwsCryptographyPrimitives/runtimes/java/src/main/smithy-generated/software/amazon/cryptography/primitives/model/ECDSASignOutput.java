// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class ECDSASignOutput {
  private final ByteBuffer signature;

  protected ECDSASignOutput(BuilderImpl builder) {
    this.signature = builder.signature();
  }

  public ByteBuffer signature() {
    return this.signature;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder signature(ByteBuffer signature);

    ByteBuffer signature();

    ECDSASignOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer signature;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ECDSASignOutput model) {
      this.signature = model.signature();
    }

    public Builder signature(ByteBuffer signature) {
      this.signature = signature;
      return this;
    }

    public ByteBuffer signature() {
      return this.signature;
    }

    public ECDSASignOutput build() {
      if (Objects.isNull(this.signature()))  {
        throw new IllegalArgumentException("Missing value for required field `signature`");
      }
      return new ECDSASignOutput(this);
    }
  }
}
