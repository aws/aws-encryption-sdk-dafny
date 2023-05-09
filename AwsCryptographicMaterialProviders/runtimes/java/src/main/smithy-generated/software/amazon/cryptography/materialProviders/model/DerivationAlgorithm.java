// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class DerivationAlgorithm {
  private final HKDF HKDF;

  private final IDENTITY IDENTITY;

  private final None None;

  protected DerivationAlgorithm(BuilderImpl builder) {
    this.HKDF = builder.HKDF();
    this.IDENTITY = builder.IDENTITY();
    this.None = builder.None();
  }

  public HKDF HKDF() {
    return this.HKDF;
  }

  public IDENTITY IDENTITY() {
    return this.IDENTITY;
  }

  public None None() {
    return this.None;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder HKDF(HKDF HKDF);

    HKDF HKDF();

    Builder IDENTITY(IDENTITY IDENTITY);

    IDENTITY IDENTITY();

    Builder None(None None);

    None None();

    DerivationAlgorithm build();
  }

  static class BuilderImpl implements Builder {
    protected HKDF HKDF;

    protected IDENTITY IDENTITY;

    protected None None;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DerivationAlgorithm model) {
      this.HKDF = model.HKDF();
      this.IDENTITY = model.IDENTITY();
      this.None = model.None();
    }

    public Builder HKDF(HKDF HKDF) {
      this.HKDF = HKDF;
      return this;
    }

    public HKDF HKDF() {
      return this.HKDF;
    }

    public Builder IDENTITY(IDENTITY IDENTITY) {
      this.IDENTITY = IDENTITY;
      return this;
    }

    public IDENTITY IDENTITY() {
      return this.IDENTITY;
    }

    public Builder None(None None) {
      this.None = None;
      return this;
    }

    public None None() {
      return this.None;
    }

    public DerivationAlgorithm build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`DerivationAlgorithm` is a Union. A Union MUST have one and only one value set.");
      }
      return new DerivationAlgorithm(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.HKDF, this.IDENTITY, this.None};
      boolean haveOneNonNull = false;
      for (Object o : allValues) {
        if (Objects.nonNull(o)) {
          if (haveOneNonNull) {
            return false;
          }
          haveOneNonNull = true;
        }
      }
      return haveOneNonNull;
    }
  }
}
