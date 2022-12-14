// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

public class GenerateRSAKeyPairOutput {
  private final RSAPublicKey publicKey;

  private final RSAPrivateKey privateKey;

  protected GenerateRSAKeyPairOutput(BuilderImpl builder) {
    this.publicKey = builder.publicKey();
    this.privateKey = builder.privateKey();
  }

  public RSAPublicKey publicKey() {
    return this.publicKey;
  }

  public RSAPrivateKey privateKey() {
    return this.privateKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder publicKey(RSAPublicKey publicKey);

    RSAPublicKey publicKey();

    Builder privateKey(RSAPrivateKey privateKey);

    RSAPrivateKey privateKey();

    GenerateRSAKeyPairOutput build();
  }

  static class BuilderImpl implements Builder {
    protected RSAPublicKey publicKey;

    protected RSAPrivateKey privateKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateRSAKeyPairOutput model) {
      this.publicKey = model.publicKey();
      this.privateKey = model.privateKey();
    }

    public Builder publicKey(RSAPublicKey publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public RSAPublicKey publicKey() {
      return this.publicKey;
    }

    public Builder privateKey(RSAPrivateKey privateKey) {
      this.privateKey = privateKey;
      return this;
    }

    public RSAPrivateKey privateKey() {
      return this.privateKey;
    }

    public GenerateRSAKeyPairOutput build() {
      if (Objects.isNull(this.publicKey()))  {
        throw new IllegalArgumentException("Missing value for required field `publicKey`");
      }
      if (Objects.isNull(this.privateKey()))  {
        throw new IllegalArgumentException("Missing value for required field `privateKey`");
      }
      return new GenerateRSAKeyPairOutput(this);
    }
  }
}
