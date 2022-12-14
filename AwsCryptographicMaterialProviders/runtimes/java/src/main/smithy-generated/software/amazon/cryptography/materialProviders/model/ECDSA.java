// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;
import software.amazon.cryptography.primitives.model.ECDSASignatureAlgorithm;

public class ECDSA {
  private final ECDSASignatureAlgorithm curve;

  protected ECDSA(BuilderImpl builder) {
    this.curve = builder.curve();
  }

  public ECDSASignatureAlgorithm curve() {
    return this.curve;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder curve(ECDSASignatureAlgorithm curve);

    ECDSASignatureAlgorithm curve();

    ECDSA build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSASignatureAlgorithm curve;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ECDSA model) {
      this.curve = model.curve();
    }

    public Builder curve(ECDSASignatureAlgorithm curve) {
      this.curve = curve;
      return this;
    }

    public ECDSASignatureAlgorithm curve() {
      return this.curve;
    }

    public ECDSA build() {
      if (Objects.isNull(this.curve()))  {
        throw new IllegalArgumentException("Missing value for required field `curve`");
      }
      return new ECDSA(this);
    }
  }
}
