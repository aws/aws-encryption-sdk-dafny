// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class IntermediateKeyWrapping {
  private final DerivationAlgorithm keyEncryptionKeyKdf;

  private final DerivationAlgorithm macKeyKdf;

  private final Encrypt pdkEncryptAlgorithm;

  protected IntermediateKeyWrapping(BuilderImpl builder) {
    this.keyEncryptionKeyKdf = builder.keyEncryptionKeyKdf();
    this.macKeyKdf = builder.macKeyKdf();
    this.pdkEncryptAlgorithm = builder.pdkEncryptAlgorithm();
  }

  public DerivationAlgorithm keyEncryptionKeyKdf() {
    return this.keyEncryptionKeyKdf;
  }

  public DerivationAlgorithm macKeyKdf() {
    return this.macKeyKdf;
  }

  public Encrypt pdkEncryptAlgorithm() {
    return this.pdkEncryptAlgorithm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyEncryptionKeyKdf(DerivationAlgorithm keyEncryptionKeyKdf);

    DerivationAlgorithm keyEncryptionKeyKdf();

    Builder macKeyKdf(DerivationAlgorithm macKeyKdf);

    DerivationAlgorithm macKeyKdf();

    Builder pdkEncryptAlgorithm(Encrypt pdkEncryptAlgorithm);

    Encrypt pdkEncryptAlgorithm();

    IntermediateKeyWrapping build();
  }

  static class BuilderImpl implements Builder {
    protected DerivationAlgorithm keyEncryptionKeyKdf;

    protected DerivationAlgorithm macKeyKdf;

    protected Encrypt pdkEncryptAlgorithm;

    protected BuilderImpl() {
    }

    protected BuilderImpl(IntermediateKeyWrapping model) {
      this.keyEncryptionKeyKdf = model.keyEncryptionKeyKdf();
      this.macKeyKdf = model.macKeyKdf();
      this.pdkEncryptAlgorithm = model.pdkEncryptAlgorithm();
    }

    public Builder keyEncryptionKeyKdf(DerivationAlgorithm keyEncryptionKeyKdf) {
      this.keyEncryptionKeyKdf = keyEncryptionKeyKdf;
      return this;
    }

    public DerivationAlgorithm keyEncryptionKeyKdf() {
      return this.keyEncryptionKeyKdf;
    }

    public Builder macKeyKdf(DerivationAlgorithm macKeyKdf) {
      this.macKeyKdf = macKeyKdf;
      return this;
    }

    public DerivationAlgorithm macKeyKdf() {
      return this.macKeyKdf;
    }

    public Builder pdkEncryptAlgorithm(Encrypt pdkEncryptAlgorithm) {
      this.pdkEncryptAlgorithm = pdkEncryptAlgorithm;
      return this;
    }

    public Encrypt pdkEncryptAlgorithm() {
      return this.pdkEncryptAlgorithm;
    }

    public IntermediateKeyWrapping build() {
      if (Objects.isNull(this.keyEncryptionKeyKdf()))  {
        throw new IllegalArgumentException("Missing value for required field `keyEncryptionKeyKdf`");
      }
      if (Objects.isNull(this.macKeyKdf()))  {
        throw new IllegalArgumentException("Missing value for required field `macKeyKdf`");
      }
      if (Objects.isNull(this.pdkEncryptAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `pdkEncryptAlgorithm`");
      }
      return new IntermediateKeyWrapping(this);
    }
  }
}
