// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.CryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.IKeyring;
import software.amazon.cryptography.materialproviders.Keyring;

public class DecryptInput {
  private final ByteBuffer ciphertext;

  private final ICryptographicMaterialsManager materialsManager;

  private final IKeyring keyring;

  private final Map<String, String> encryptionContext;

  protected DecryptInput(BuilderImpl builder) {
    this.ciphertext = builder.ciphertext();
    this.materialsManager = builder.materialsManager();
    this.keyring = builder.keyring();
    this.encryptionContext = builder.encryptionContext();
  }

  public ByteBuffer ciphertext() {
    return this.ciphertext;
  }

  public ICryptographicMaterialsManager materialsManager() {
    return this.materialsManager;
  }

  public IKeyring keyring() {
    return this.keyring;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ciphertext(ByteBuffer ciphertext);

    ByteBuffer ciphertext();

    Builder materialsManager(ICryptographicMaterialsManager materialsManager);

    ICryptographicMaterialsManager materialsManager();

    Builder keyring(IKeyring keyring);

    IKeyring keyring();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    DecryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer ciphertext;

    protected ICryptographicMaterialsManager materialsManager;

    protected IKeyring keyring;

    protected Map<String, String> encryptionContext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DecryptInput model) {
      this.ciphertext = model.ciphertext();
      this.materialsManager = model.materialsManager();
      this.keyring = model.keyring();
      this.encryptionContext = model.encryptionContext();
    }

    public Builder ciphertext(ByteBuffer ciphertext) {
      this.ciphertext = ciphertext;
      return this;
    }

    public ByteBuffer ciphertext() {
      return this.ciphertext;
    }

    public Builder materialsManager(ICryptographicMaterialsManager materialsManager) {
      this.materialsManager = CryptographicMaterialsManager.wrap(materialsManager);
      return this;
    }

    public ICryptographicMaterialsManager materialsManager() {
      return this.materialsManager;
    }

    public Builder keyring(IKeyring keyring) {
      this.keyring = Keyring.wrap(keyring);
      return this;
    }

    public IKeyring keyring() {
      return this.keyring;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public DecryptInput build() {
      if (Objects.isNull(this.ciphertext()))  {
        throw new IllegalArgumentException("Missing value for required field `ciphertext`");
      }
      return new DecryptInput(this);
    }
  }
}
