// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;
import software.amazon.cryptography.materialProviders.IKeyring;
import software.amazon.cryptography.materialProviders.Keyring;

public class CreateDefaultCryptographicMaterialsManagerInput {
  private final Keyring keyring;

  protected CreateDefaultCryptographicMaterialsManagerInput(BuilderImpl builder) {
    this.keyring = builder.keyring();
  }

  public Keyring keyring() {
    return this.keyring;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyring(IKeyring keyring);

    Keyring keyring();

    CreateDefaultCryptographicMaterialsManagerInput build();
  }

  static class BuilderImpl implements Builder {
    protected Keyring keyring;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateDefaultCryptographicMaterialsManagerInput model) {
      this.keyring = model.keyring();
    }

    public Builder keyring(IKeyring keyring) {
      this.keyring = Keyring.wrap(keyring);
      return this;
    }

    public Keyring keyring() {
      return this.keyring;
    }

    public CreateDefaultCryptographicMaterialsManagerInput build() {
      if (Objects.isNull(this.keyring()))  {
        throw new IllegalArgumentException("Missing value for required field `keyring`");
      }
      return new CreateDefaultCryptographicMaterialsManagerInput(this);
    }
  }
}
