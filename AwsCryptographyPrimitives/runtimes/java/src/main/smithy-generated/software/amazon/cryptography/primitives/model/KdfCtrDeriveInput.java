// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class KdfCtrDeriveInput {
  private final HMacInput macAlgorithm;

  private final ByteBuffer iv;

  private final ByteBuffer ikm;

  protected KdfCtrDeriveInput(BuilderImpl builder) {
    this.macAlgorithm = builder.macAlgorithm();
    this.iv = builder.iv();
    this.ikm = builder.ikm();
  }

  public HMacInput macAlgorithm() {
    return this.macAlgorithm;
  }

  public ByteBuffer iv() {
    return this.iv;
  }

  public ByteBuffer ikm() {
    return this.ikm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder macAlgorithm(HMacInput macAlgorithm);

    HMacInput macAlgorithm();

    Builder iv(ByteBuffer iv);

    ByteBuffer iv();

    Builder ikm(ByteBuffer ikm);

    ByteBuffer ikm();

    KdfCtrDeriveInput build();
  }

  static class BuilderImpl implements Builder {
    protected HMacInput macAlgorithm;

    protected ByteBuffer iv;

    protected ByteBuffer ikm;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KdfCtrDeriveInput model) {
      this.macAlgorithm = model.macAlgorithm();
      this.iv = model.iv();
      this.ikm = model.ikm();
    }

    public Builder macAlgorithm(HMacInput macAlgorithm) {
      this.macAlgorithm = macAlgorithm;
      return this;
    }

    public HMacInput macAlgorithm() {
      return this.macAlgorithm;
    }

    public Builder iv(ByteBuffer iv) {
      this.iv = iv;
      return this;
    }

    public ByteBuffer iv() {
      return this.iv;
    }

    public Builder ikm(ByteBuffer ikm) {
      this.ikm = ikm;
      return this;
    }

    public ByteBuffer ikm() {
      return this.ikm;
    }

    public KdfCtrDeriveInput build() {
      if (Objects.isNull(this.macAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `macAlgorithm`");
      }
      if (Objects.isNull(this.ikm()))  {
        throw new IllegalArgumentException("Missing value for required field `ikm`");
      }
      return new KdfCtrDeriveInput(this);
    }
  }
}
