// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.CryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.IKeyring;
import software.amazon.cryptography.materialproviders.Keyring;

public class CreateExpectedEncryptionContextCMMInput {
  private final ICryptographicMaterialsManager underlyingCMM;

  private final IKeyring keyring;

  private final List<String> requiredEncryptionContextKeys;

  protected CreateExpectedEncryptionContextCMMInput(BuilderImpl builder) {
    this.underlyingCMM = builder.underlyingCMM();
    this.keyring = builder.keyring();
    this.requiredEncryptionContextKeys = builder.requiredEncryptionContextKeys();
  }

  public ICryptographicMaterialsManager underlyingCMM() {
    return this.underlyingCMM;
  }

  public IKeyring keyring() {
    return this.keyring;
  }

  public List<String> requiredEncryptionContextKeys() {
    return this.requiredEncryptionContextKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder underlyingCMM(ICryptographicMaterialsManager underlyingCMM);

    ICryptographicMaterialsManager underlyingCMM();

    Builder keyring(IKeyring keyring);

    IKeyring keyring();

    Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys);

    List<String> requiredEncryptionContextKeys();

    CreateExpectedEncryptionContextCMMInput build();
  }

  static class BuilderImpl implements Builder {
    protected ICryptographicMaterialsManager underlyingCMM;

    protected IKeyring keyring;

    protected List<String> requiredEncryptionContextKeys;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateExpectedEncryptionContextCMMInput model) {
      this.underlyingCMM = model.underlyingCMM();
      this.keyring = model.keyring();
      this.requiredEncryptionContextKeys = model.requiredEncryptionContextKeys();
    }

    public Builder underlyingCMM(ICryptographicMaterialsManager underlyingCMM) {
      this.underlyingCMM = CryptographicMaterialsManager.wrap(underlyingCMM);
      return this;
    }

    public ICryptographicMaterialsManager underlyingCMM() {
      return this.underlyingCMM;
    }

    public Builder keyring(IKeyring keyring) {
      this.keyring = Keyring.wrap(keyring);
      return this;
    }

    public IKeyring keyring() {
      return this.keyring;
    }

    public Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys) {
      this.requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      return this;
    }

    public List<String> requiredEncryptionContextKeys() {
      return this.requiredEncryptionContextKeys;
    }

    public CreateExpectedEncryptionContextCMMInput build() {
      if (Objects.isNull(this.requiredEncryptionContextKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `requiredEncryptionContextKeys`");
      }
      return new CreateExpectedEncryptionContextCMMInput(this);
    }
  }
}
