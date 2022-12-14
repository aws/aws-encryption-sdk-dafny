// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GenerateECDSASignatureKeyOutput {
  private final ECDSASignatureAlgorithm signatureAlgorithm;

  private final ByteBuffer verificationKey;

  private final ByteBuffer signingKey;

  protected GenerateECDSASignatureKeyOutput(BuilderImpl builder) {
    this.signatureAlgorithm = builder.signatureAlgorithm();
    this.verificationKey = builder.verificationKey();
    this.signingKey = builder.signingKey();
  }

  public ECDSASignatureAlgorithm signatureAlgorithm() {
    return this.signatureAlgorithm;
  }

  public ByteBuffer verificationKey() {
    return this.verificationKey;
  }

  public ByteBuffer signingKey() {
    return this.signingKey;
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

    Builder verificationKey(ByteBuffer verificationKey);

    ByteBuffer verificationKey();

    Builder signingKey(ByteBuffer signingKey);

    ByteBuffer signingKey();

    GenerateECDSASignatureKeyOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSASignatureAlgorithm signatureAlgorithm;

    protected ByteBuffer verificationKey;

    protected ByteBuffer signingKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateECDSASignatureKeyOutput model) {
      this.signatureAlgorithm = model.signatureAlgorithm();
      this.verificationKey = model.verificationKey();
      this.signingKey = model.signingKey();
    }

    public Builder signatureAlgorithm(ECDSASignatureAlgorithm signatureAlgorithm) {
      this.signatureAlgorithm = signatureAlgorithm;
      return this;
    }

    public ECDSASignatureAlgorithm signatureAlgorithm() {
      return this.signatureAlgorithm;
    }

    public Builder verificationKey(ByteBuffer verificationKey) {
      this.verificationKey = verificationKey;
      return this;
    }

    public ByteBuffer verificationKey() {
      return this.verificationKey;
    }

    public Builder signingKey(ByteBuffer signingKey) {
      this.signingKey = signingKey;
      return this;
    }

    public ByteBuffer signingKey() {
      return this.signingKey;
    }

    public GenerateECDSASignatureKeyOutput build() {
      if (Objects.isNull(this.signatureAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `signatureAlgorithm`");
      }
      if (Objects.isNull(this.verificationKey()))  {
        throw new IllegalArgumentException("Missing value for required field `verificationKey`");
      }
      if (Objects.isNull(this.signingKey()))  {
        throw new IllegalArgumentException("Missing value for required field `signingKey`");
      }
      return new GenerateECDSASignatureKeyOutput(this);
    }
  }
}
