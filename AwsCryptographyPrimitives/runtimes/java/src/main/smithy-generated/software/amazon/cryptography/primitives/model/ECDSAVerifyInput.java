// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class ECDSAVerifyInput {
  private final ECDSASignatureAlgorithm signatureAlgorithm;

  private final ByteBuffer verificationKey;

  private final ByteBuffer message;

  private final ByteBuffer signature;

  protected ECDSAVerifyInput(BuilderImpl builder) {
    this.signatureAlgorithm = builder.signatureAlgorithm();
    this.verificationKey = builder.verificationKey();
    this.message = builder.message();
    this.signature = builder.signature();
  }

  public ECDSASignatureAlgorithm signatureAlgorithm() {
    return this.signatureAlgorithm;
  }

  public ByteBuffer verificationKey() {
    return this.verificationKey;
  }

  public ByteBuffer message() {
    return this.message;
  }

  public ByteBuffer signature() {
    return this.signature;
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

    Builder message(ByteBuffer message);

    ByteBuffer message();

    Builder signature(ByteBuffer signature);

    ByteBuffer signature();

    ECDSAVerifyInput build();
  }

  static class BuilderImpl implements Builder {
    protected ECDSASignatureAlgorithm signatureAlgorithm;

    protected ByteBuffer verificationKey;

    protected ByteBuffer message;

    protected ByteBuffer signature;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ECDSAVerifyInput model) {
      this.signatureAlgorithm = model.signatureAlgorithm();
      this.verificationKey = model.verificationKey();
      this.message = model.message();
      this.signature = model.signature();
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

    public Builder message(ByteBuffer message) {
      this.message = message;
      return this;
    }

    public ByteBuffer message() {
      return this.message;
    }

    public Builder signature(ByteBuffer signature) {
      this.signature = signature;
      return this;
    }

    public ByteBuffer signature() {
      return this.signature;
    }

    public ECDSAVerifyInput build() {
      if (Objects.isNull(this.signatureAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `signatureAlgorithm`");
      }
      if (Objects.isNull(this.verificationKey()))  {
        throw new IllegalArgumentException("Missing value for required field `verificationKey`");
      }
      if (Objects.isNull(this.message()))  {
        throw new IllegalArgumentException("Missing value for required field `message`");
      }
      if (Objects.isNull(this.signature()))  {
        throw new IllegalArgumentException("Missing value for required field `signature`");
      }
      return new ECDSAVerifyInput(this);
    }
  }
}
