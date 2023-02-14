// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AlgorithmSuiteInfo {
  private final AlgorithmSuiteId id;

  private final ByteBuffer binaryId;

  private final Integer messageVersion;

  private final Encrypt encrypt;

  private final DerivationAlgorithm kdf;

  private final DerivationAlgorithm commitment;

  private final SignatureAlgorithm signature;

  private final SymmetricSignatureAlgorithm symmetricSignature;

  private final EdkWrappingAlgorithm edkWrapping;

  protected AlgorithmSuiteInfo(BuilderImpl builder) {
    this.id = builder.id();
    this.binaryId = builder.binaryId();
    this.messageVersion = builder.messageVersion();
    this.encrypt = builder.encrypt();
    this.kdf = builder.kdf();
    this.commitment = builder.commitment();
    this.signature = builder.signature();
    this.symmetricSignature = builder.symmetricSignature();
    this.edkWrapping = builder.edkWrapping();
  }

  public AlgorithmSuiteId id() {
    return this.id;
  }

  public ByteBuffer binaryId() {
    return this.binaryId;
  }

  public Integer messageVersion() {
    return this.messageVersion;
  }

  public Encrypt encrypt() {
    return this.encrypt;
  }

  public DerivationAlgorithm kdf() {
    return this.kdf;
  }

  public DerivationAlgorithm commitment() {
    return this.commitment;
  }

  public SignatureAlgorithm signature() {
    return this.signature;
  }

  public SymmetricSignatureAlgorithm symmetricSignature() {
    return this.symmetricSignature;
  }

  public EdkWrappingAlgorithm edkWrapping() {
    return this.edkWrapping;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder id(AlgorithmSuiteId id);

    AlgorithmSuiteId id();

    Builder binaryId(ByteBuffer binaryId);

    ByteBuffer binaryId();

    Builder messageVersion(Integer messageVersion);

    Integer messageVersion();

    Builder encrypt(Encrypt encrypt);

    Encrypt encrypt();

    Builder kdf(DerivationAlgorithm kdf);

    DerivationAlgorithm kdf();

    Builder commitment(DerivationAlgorithm commitment);

    DerivationAlgorithm commitment();

    Builder signature(SignatureAlgorithm signature);

    SignatureAlgorithm signature();

    Builder symmetricSignature(SymmetricSignatureAlgorithm symmetricSignature);

    SymmetricSignatureAlgorithm symmetricSignature();

    Builder edkWrapping(EdkWrappingAlgorithm edkWrapping);

    EdkWrappingAlgorithm edkWrapping();

    AlgorithmSuiteInfo build();
  }

  static class BuilderImpl implements Builder {
    protected AlgorithmSuiteId id;

    protected ByteBuffer binaryId;

    protected Integer messageVersion;

    protected Encrypt encrypt;

    protected DerivationAlgorithm kdf;

    protected DerivationAlgorithm commitment;

    protected SignatureAlgorithm signature;

    protected SymmetricSignatureAlgorithm symmetricSignature;

    protected EdkWrappingAlgorithm edkWrapping;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AlgorithmSuiteInfo model) {
      this.id = model.id();
      this.binaryId = model.binaryId();
      this.messageVersion = model.messageVersion();
      this.encrypt = model.encrypt();
      this.kdf = model.kdf();
      this.commitment = model.commitment();
      this.signature = model.signature();
      this.symmetricSignature = model.symmetricSignature();
      this.edkWrapping = model.edkWrapping();
    }

    public Builder id(AlgorithmSuiteId id) {
      this.id = id;
      return this;
    }

    public AlgorithmSuiteId id() {
      return this.id;
    }

    public Builder binaryId(ByteBuffer binaryId) {
      this.binaryId = binaryId;
      return this;
    }

    public ByteBuffer binaryId() {
      return this.binaryId;
    }

    public Builder messageVersion(Integer messageVersion) {
      this.messageVersion = messageVersion;
      return this;
    }

    public Integer messageVersion() {
      return this.messageVersion;
    }

    public Builder encrypt(Encrypt encrypt) {
      this.encrypt = encrypt;
      return this;
    }

    public Encrypt encrypt() {
      return this.encrypt;
    }

    public Builder kdf(DerivationAlgorithm kdf) {
      this.kdf = kdf;
      return this;
    }

    public DerivationAlgorithm kdf() {
      return this.kdf;
    }

    public Builder commitment(DerivationAlgorithm commitment) {
      this.commitment = commitment;
      return this;
    }

    public DerivationAlgorithm commitment() {
      return this.commitment;
    }

    public Builder signature(SignatureAlgorithm signature) {
      this.signature = signature;
      return this;
    }

    public SignatureAlgorithm signature() {
      return this.signature;
    }

    public Builder symmetricSignature(SymmetricSignatureAlgorithm symmetricSignature) {
      this.symmetricSignature = symmetricSignature;
      return this;
    }

    public SymmetricSignatureAlgorithm symmetricSignature() {
      return this.symmetricSignature;
    }

    public Builder edkWrapping(EdkWrappingAlgorithm edkWrapping) {
      this.edkWrapping = edkWrapping;
      return this;
    }

    public EdkWrappingAlgorithm edkWrapping() {
      return this.edkWrapping;
    }

    public AlgorithmSuiteInfo build() {
      if (Objects.isNull(this.id()))  {
        throw new IllegalArgumentException("Missing value for required field `id`");
      }
      if (Objects.isNull(this.binaryId()))  {
        throw new IllegalArgumentException("Missing value for required field `binaryId`");
      }
      if (Objects.isNull(this.messageVersion()))  {
        throw new IllegalArgumentException("Missing value for required field `messageVersion`");
      }
      if (Objects.isNull(this.encrypt()))  {
        throw new IllegalArgumentException("Missing value for required field `encrypt`");
      }
      if (Objects.isNull(this.kdf()))  {
        throw new IllegalArgumentException("Missing value for required field `kdf`");
      }
      if (Objects.isNull(this.commitment()))  {
        throw new IllegalArgumentException("Missing value for required field `commitment`");
      }
      if (Objects.isNull(this.signature()))  {
        throw new IllegalArgumentException("Missing value for required field `signature`");
      }
      if (Objects.isNull(this.symmetricSignature()))  {
        throw new IllegalArgumentException("Missing value for required field `symmetricSignature`");
      }
      if (Objects.isNull(this.edkWrapping()))  {
        throw new IllegalArgumentException("Missing value for required field `edkWrapping`");
      }
      return new AlgorithmSuiteInfo(this);
    }
  }
}
