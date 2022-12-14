// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class DecryptMaterialsOutput {
  private final DecryptionMaterials decryptionMaterials;

  protected DecryptMaterialsOutput(BuilderImpl builder) {
    this.decryptionMaterials = builder.decryptionMaterials();
  }

  public DecryptionMaterials decryptionMaterials() {
    return this.decryptionMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder decryptionMaterials(DecryptionMaterials decryptionMaterials);

    DecryptionMaterials decryptionMaterials();

    DecryptMaterialsOutput build();
  }

  static class BuilderImpl implements Builder {
    protected DecryptionMaterials decryptionMaterials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptMaterialsOutput model) {
      this.decryptionMaterials = model.decryptionMaterials();
    }

    public Builder decryptionMaterials(DecryptionMaterials decryptionMaterials) {
      this.decryptionMaterials = decryptionMaterials;
      return this;
    }

    public DecryptionMaterials decryptionMaterials() {
      return this.decryptionMaterials;
    }

    public DecryptMaterialsOutput build() {
      if (Objects.isNull(this.decryptionMaterials()))  {
        throw new IllegalArgumentException("Missing value for required field `decryptionMaterials`");
      }
      return new DecryptMaterialsOutput(this);
    }
  }
}
