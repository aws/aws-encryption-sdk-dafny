// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class Materials {
  private final EncryptionMaterials Encryption;

  private final DecryptionMaterials Decryption;

  private final HierarchicalMaterials Hierarchical;

  protected Materials(BuilderImpl builder) {
    this.Encryption = builder.Encryption();
    this.Decryption = builder.Decryption();
    this.Hierarchical = builder.Hierarchical();
  }

  public EncryptionMaterials Encryption() {
    return this.Encryption;
  }

  public DecryptionMaterials Decryption() {
    return this.Decryption;
  }

  public HierarchicalMaterials Hierarchical() {
    return this.Hierarchical;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder Encryption(EncryptionMaterials Encryption);

    EncryptionMaterials Encryption();

    Builder Decryption(DecryptionMaterials Decryption);

    DecryptionMaterials Decryption();

    Builder Hierarchical(HierarchicalMaterials Hierarchical);

    HierarchicalMaterials Hierarchical();

    Materials build();
  }

  static class BuilderImpl implements Builder {
    protected EncryptionMaterials Encryption;

    protected DecryptionMaterials Decryption;

    protected HierarchicalMaterials Hierarchical;

    protected BuilderImpl() {
    }

    protected BuilderImpl(Materials model) {
      this.Encryption = model.Encryption();
      this.Decryption = model.Decryption();
      this.Hierarchical = model.Hierarchical();
    }

    public Builder Encryption(EncryptionMaterials Encryption) {
      this.Encryption = Encryption;
      return this;
    }

    public EncryptionMaterials Encryption() {
      return this.Encryption;
    }

    public Builder Decryption(DecryptionMaterials Decryption) {
      this.Decryption = Decryption;
      return this;
    }

    public DecryptionMaterials Decryption() {
      return this.Decryption;
    }

    public Builder Hierarchical(HierarchicalMaterials Hierarchical) {
      this.Hierarchical = Hierarchical;
      return this;
    }

    public HierarchicalMaterials Hierarchical() {
      return this.Hierarchical;
    }

    public Materials build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`Materials` is a Union. A Union MUST have one and only one value set.");
      }
      return new Materials(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.Encryption, this.Decryption, this.Hierarchical};
      boolean haveOneNonNull = false;
      for (Object o : allValues) {
        if (Objects.nonNull(o)) {
          if (haveOneNonNull) {
            return false;
          }
          haveOneNonNull = true;
        }
      }
      return haveOneNonNull;
    }
  }
}
