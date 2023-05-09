// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class OnDecryptOutput {
  private final DecryptionMaterials materials;

  protected OnDecryptOutput(BuilderImpl builder) {
    this.materials = builder.materials();
  }

  public DecryptionMaterials materials() {
    return this.materials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder materials(DecryptionMaterials materials);

    DecryptionMaterials materials();

    OnDecryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected DecryptionMaterials materials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(OnDecryptOutput model) {
      this.materials = model.materials();
    }

    public Builder materials(DecryptionMaterials materials) {
      this.materials = materials;
      return this;
    }

    public DecryptionMaterials materials() {
      return this.materials;
    }

    public OnDecryptOutput build() {
      if (Objects.isNull(this.materials()))  {
        throw new IllegalArgumentException("Missing value for required field `materials`");
      }
      return new OnDecryptOutput(this);
    }
  }
}
