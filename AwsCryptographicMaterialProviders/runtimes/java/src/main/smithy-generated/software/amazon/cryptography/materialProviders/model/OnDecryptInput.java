// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;

public class OnDecryptInput {
  private final DecryptionMaterials materials;

  private final List<EncryptedDataKey> encryptedDataKeys;

  protected OnDecryptInput(BuilderImpl builder) {
    this.materials = builder.materials();
    this.encryptedDataKeys = builder.encryptedDataKeys();
  }

  public DecryptionMaterials materials() {
    return this.materials;
  }

  public List<EncryptedDataKey> encryptedDataKeys() {
    return this.encryptedDataKeys;
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

    Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys);

    List<EncryptedDataKey> encryptedDataKeys();

    OnDecryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected DecryptionMaterials materials;

    protected List<EncryptedDataKey> encryptedDataKeys;

    protected BuilderImpl() {
    }

    protected BuilderImpl(OnDecryptInput model) {
      this.materials = model.materials();
      this.encryptedDataKeys = model.encryptedDataKeys();
    }

    public Builder materials(DecryptionMaterials materials) {
      this.materials = materials;
      return this;
    }

    public DecryptionMaterials materials() {
      return this.materials;
    }

    public Builder encryptedDataKeys(List<EncryptedDataKey> encryptedDataKeys) {
      this.encryptedDataKeys = encryptedDataKeys;
      return this;
    }

    public List<EncryptedDataKey> encryptedDataKeys() {
      return this.encryptedDataKeys;
    }

    public OnDecryptInput build() {
      if (Objects.isNull(this.materials()))  {
        throw new IllegalArgumentException("Missing value for required field `materials`");
      }
      if (Objects.isNull(this.encryptedDataKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptedDataKeys`");
      }
      return new OnDecryptInput(this);
    }
  }
}
