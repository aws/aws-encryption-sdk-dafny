// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class SignatureAlgorithm {
  private final ECDSA ECDSA;

  private final None None;

  protected SignatureAlgorithm(BuilderImpl builder) {
    this.ECDSA = builder.ECDSA();
    this.None = builder.None();
  }

  public ECDSA ECDSA() {
    return this.ECDSA;
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
    Builder ECDSA(ECDSA ECDSA);

    ECDSA ECDSA();

    Builder None(None None);

    None None();

    SignatureAlgorithm build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSA ECDSA;

    protected None None;

    protected BuilderImpl() {
    }

    protected BuilderImpl(SignatureAlgorithm model) {
      this.ECDSA = model.ECDSA();
      this.None = model.None();
    }

    public Builder ECDSA(ECDSA ECDSA) {
      this.ECDSA = ECDSA;
      return this;
    }

    public ECDSA ECDSA() {
      return this.ECDSA;
    }

    public Builder None(None None) {
      this.None = None;
      return this;
    }

    public None None() {
      return this.None;
    }

    public SignatureAlgorithm build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`SignatureAlgorithm` is a Union. A Union MUST have one and only one value set.");
      }
      return new SignatureAlgorithm(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.ECDSA, this.None};
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
