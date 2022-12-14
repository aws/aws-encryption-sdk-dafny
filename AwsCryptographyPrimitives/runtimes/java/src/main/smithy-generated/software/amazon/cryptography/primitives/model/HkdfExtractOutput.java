// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class HkdfExtractOutput {
  private final ByteBuffer prk;

  protected HkdfExtractOutput(BuilderImpl builder) {
    this.prk = builder.prk();
  }

  public ByteBuffer prk() {
    return this.prk;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder prk(ByteBuffer prk);

    ByteBuffer prk();

    HkdfExtractOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer prk;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HkdfExtractOutput model) {
      this.prk = model.prk();
    }

    public Builder prk(ByteBuffer prk) {
      this.prk = prk;
      return this;
    }

    public ByteBuffer prk() {
      return this.prk;
    }

    public HkdfExtractOutput build() {
      if (Objects.isNull(this.prk()))  {
        throw new IllegalArgumentException("Missing value for required field `prk`");
      }
      return new HkdfExtractOutput(this);
    }
  }
}
