// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

public class GenerateECDSASignatureKeyInput {
  private final ECDSASignatureAlgorithm signatureAlgorithm;

  protected GenerateECDSASignatureKeyInput(BuilderImpl builder) {
    this.signatureAlgorithm = builder.signatureAlgorithm();
  }

  public ECDSASignatureAlgorithm signatureAlgorithm() {
    return this.signatureAlgorithm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder signatureAlgorithm(ECDSASignatureAlgorithm signatureAlgorithm);

    ECDSASignatureAlgorithm signatureAlgorithm();

    GenerateECDSASignatureKeyInput build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSASignatureAlgorithm signatureAlgorithm;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateECDSASignatureKeyInput model) {
      this.signatureAlgorithm = model.signatureAlgorithm();
    }

    public Builder signatureAlgorithm(ECDSASignatureAlgorithm signatureAlgorithm) {
      this.signatureAlgorithm = signatureAlgorithm;
      return this;
    }

    public ECDSASignatureAlgorithm signatureAlgorithm() {
      return this.signatureAlgorithm;
    }

    public GenerateECDSASignatureKeyInput build() {
      if (Objects.isNull(this.signatureAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `signatureAlgorithm`");
      }
      return new GenerateECDSASignatureKeyInput(this);
    }
  }
}
