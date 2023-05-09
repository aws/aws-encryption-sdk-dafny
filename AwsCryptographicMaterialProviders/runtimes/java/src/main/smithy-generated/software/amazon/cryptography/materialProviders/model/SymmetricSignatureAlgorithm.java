// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;
import software.amazon.cryptography.primitives.model.DigestAlgorithm;

public class SymmetricSignatureAlgorithm {
  private final DigestAlgorithm HMAC;

  private final None None;

  protected SymmetricSignatureAlgorithm(BuilderImpl builder) {
    this.HMAC = builder.HMAC();
    this.None = builder.None();
  }

  public DigestAlgorithm HMAC() {
    return this.HMAC;
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
    Builder HMAC(DigestAlgorithm HMAC);

    DigestAlgorithm HMAC();

    Builder None(None None);

    None None();

    SymmetricSignatureAlgorithm build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm HMAC;

    protected None None;

    protected BuilderImpl() {
    }

    protected BuilderImpl(SymmetricSignatureAlgorithm model) {
      this.HMAC = model.HMAC();
      this.None = model.None();
    }

    public Builder HMAC(DigestAlgorithm HMAC) {
      this.HMAC = HMAC;
      return this;
    }

    public DigestAlgorithm HMAC() {
      return this.HMAC;
    }

    public Builder None(None None) {
      this.None = None;
      return this;
    }

    public None None() {
      return this.None;
    }

    public SymmetricSignatureAlgorithm build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`SymmetricSignatureAlgorithm` is a Union. A Union MUST have one and only one value set.");
      }
      return new SymmetricSignatureAlgorithm(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.HMAC, this.None};
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
