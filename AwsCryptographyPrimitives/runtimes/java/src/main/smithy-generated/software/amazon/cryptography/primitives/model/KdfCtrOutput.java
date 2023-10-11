// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class KdfCtrOutput {
  private final ByteBuffer okm;

  protected KdfCtrOutput(BuilderImpl builder) {
    this.okm = builder.okm();
  }

  public ByteBuffer okm() {
    return this.okm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder okm(ByteBuffer okm);

    ByteBuffer okm();

    KdfCtrOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer okm;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KdfCtrOutput model) {
      this.okm = model.okm();
    }

    public Builder okm(ByteBuffer okm) {
      this.okm = okm;
      return this;
    }

    public ByteBuffer okm() {
      return this.okm;
    }

    public KdfCtrOutput build() {
      if (Objects.isNull(this.okm()))  {
        throw new IllegalArgumentException("Missing value for required field `okm`");
      }
      return new KdfCtrOutput(this);
    }
  }
}
