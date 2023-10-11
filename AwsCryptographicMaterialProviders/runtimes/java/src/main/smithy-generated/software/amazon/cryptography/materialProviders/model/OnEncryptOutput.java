// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class OnEncryptOutput {
  private final EncryptionMaterials materials;

  protected OnEncryptOutput(BuilderImpl builder) {
    this.materials = builder.materials();
  }

  public EncryptionMaterials materials() {
    return this.materials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder materials(EncryptionMaterials materials);

    EncryptionMaterials materials();

    OnEncryptOutput build();
  }

  static class BuilderImpl implements Builder {
    protected EncryptionMaterials materials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(OnEncryptOutput model) {
      this.materials = model.materials();
    }

    public Builder materials(EncryptionMaterials materials) {
      this.materials = materials;
      return this;
    }

    public EncryptionMaterials materials() {
      return this.materials;
    }

    public OnEncryptOutput build() {
      if (Objects.isNull(this.materials()))  {
        throw new IllegalArgumentException("Missing value for required field `materials`");
      }
      return new OnEncryptOutput(this);
    }
  }
}
