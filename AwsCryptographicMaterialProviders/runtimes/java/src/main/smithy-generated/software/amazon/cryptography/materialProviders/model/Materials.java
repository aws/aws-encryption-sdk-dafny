// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class Materials {
  private final EncryptionMaterials Encryption;

  private final DecryptionMaterials Decryption;

  private final BranchKeyMaterials BranchKey;

  private final BeaconKeyMaterials BeaconKey;

  protected Materials(BuilderImpl builder) {
    this.Encryption = builder.Encryption();
    this.Decryption = builder.Decryption();
    this.BranchKey = builder.BranchKey();
    this.BeaconKey = builder.BeaconKey();
  }

  public EncryptionMaterials Encryption() {
    return this.Encryption;
  }

  public DecryptionMaterials Decryption() {
    return this.Decryption;
  }

  public BranchKeyMaterials BranchKey() {
    return this.BranchKey;
  }

  public BeaconKeyMaterials BeaconKey() {
    return this.BeaconKey;
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

    Builder BranchKey(BranchKeyMaterials BranchKey);

    BranchKeyMaterials BranchKey();

    Builder BeaconKey(BeaconKeyMaterials BeaconKey);

    BeaconKeyMaterials BeaconKey();

    Materials build();
  }

  static class BuilderImpl implements Builder {
    protected EncryptionMaterials Encryption;

    protected DecryptionMaterials Decryption;

    protected BranchKeyMaterials BranchKey;

    protected BeaconKeyMaterials BeaconKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(Materials model) {
      this.Encryption = model.Encryption();
      this.Decryption = model.Decryption();
      this.BranchKey = model.BranchKey();
      this.BeaconKey = model.BeaconKey();
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

    public Builder BranchKey(BranchKeyMaterials BranchKey) {
      this.BranchKey = BranchKey;
      return this;
    }

    public BranchKeyMaterials BranchKey() {
      return this.BranchKey;
    }

    public Builder BeaconKey(BeaconKeyMaterials BeaconKey) {
      this.BeaconKey = BeaconKey;
      return this;
    }

    public BeaconKeyMaterials BeaconKey() {
      return this.BeaconKey;
    }

    public Materials build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`Materials` is a Union. A Union MUST have one and only one value set.");
      }
      return new Materials(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.Encryption, this.Decryption, this.BranchKey, this.BeaconKey};
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
