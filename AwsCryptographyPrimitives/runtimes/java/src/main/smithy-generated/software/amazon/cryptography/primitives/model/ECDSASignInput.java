// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class ECDSASignInput {
  private final ECDSASignatureAlgorithm signatureAlgorithm;

  private final ByteBuffer signingKey;

  private final ByteBuffer message;

  protected ECDSASignInput(BuilderImpl builder) {
    this.signatureAlgorithm = builder.signatureAlgorithm();
    this.signingKey = builder.signingKey();
    this.message = builder.message();
  }

  public ECDSASignatureAlgorithm signatureAlgorithm() {
    return this.signatureAlgorithm;
  }

  public ByteBuffer signingKey() {
    return this.signingKey;
  }

  public ByteBuffer message() {
    return this.message;
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

    Builder signingKey(ByteBuffer signingKey);

    ByteBuffer signingKey();

    Builder message(ByteBuffer message);

    ByteBuffer message();

    ECDSASignInput build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSASignatureAlgorithm signatureAlgorithm;

    protected ByteBuffer signingKey;

    protected ByteBuffer message;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ECDSASignInput model) {
      this.signatureAlgorithm = model.signatureAlgorithm();
      this.signingKey = model.signingKey();
      this.message = model.message();
    }

    public Builder signatureAlgorithm(ECDSASignatureAlgorithm signatureAlgorithm) {
      this.signatureAlgorithm = signatureAlgorithm;
      return this;
    }

    public ECDSASignatureAlgorithm signatureAlgorithm() {
      return this.signatureAlgorithm;
    }

    public Builder signingKey(ByteBuffer signingKey) {
      this.signingKey = signingKey;
      return this;
    }

    public ByteBuffer signingKey() {
      return this.signingKey;
    }

    public Builder message(ByteBuffer message) {
      this.message = message;
      return this;
    }

    public ByteBuffer message() {
      return this.message;
    }

    public ECDSASignInput build() {
      if (Objects.isNull(this.signatureAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `signatureAlgorithm`");
      }
      if (Objects.isNull(this.signingKey()))  {
        throw new IllegalArgumentException("Missing value for required field `signingKey`");
      }
      if (Objects.isNull(this.message()))  {
        throw new IllegalArgumentException("Missing value for required field `message`");
      }
      return new ECDSASignInput(this);
    }
  }
}
