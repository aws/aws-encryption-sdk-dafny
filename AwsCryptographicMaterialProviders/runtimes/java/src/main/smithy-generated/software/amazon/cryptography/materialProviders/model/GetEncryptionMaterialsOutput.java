// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class GetEncryptionMaterialsOutput {
  private final EncryptionMaterials encryptionMaterials;

  protected GetEncryptionMaterialsOutput(BuilderImpl builder) {
    this.encryptionMaterials = builder.encryptionMaterials();
  }

  public EncryptionMaterials encryptionMaterials() {
    return this.encryptionMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder encryptionMaterials(EncryptionMaterials encryptionMaterials);

    EncryptionMaterials encryptionMaterials();

    GetEncryptionMaterialsOutput build();
  }

  static class BuilderImpl implements Builder {
    protected EncryptionMaterials encryptionMaterials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetEncryptionMaterialsOutput model) {
      this.encryptionMaterials = model.encryptionMaterials();
    }

    public Builder encryptionMaterials(EncryptionMaterials encryptionMaterials) {
      this.encryptionMaterials = encryptionMaterials;
      return this;
    }

    public EncryptionMaterials encryptionMaterials() {
      return this.encryptionMaterials;
    }

    public GetEncryptionMaterialsOutput build() {
      if (Objects.isNull(this.encryptionMaterials()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionMaterials`");
      }
      return new GetEncryptionMaterialsOutput(this);
    }
  }
}
