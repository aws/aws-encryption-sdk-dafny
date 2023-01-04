// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import Dafny.Aws.Cryptography.MaterialProviders.MaterialProvidersClient;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IAwsCryptographicMaterialProvidersClient;
import Dafny.Aws.Cryptography.MaterialProviders.__default;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import dafny.Tuple0;
import java.lang.Byte;
import java.lang.IllegalArgumentException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialProviders.model.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialProviders.model.CreateMultiKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialProviders.model.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialProviders.model.DecryptionMaterials;
import software.amazon.cryptography.materialProviders.model.EncryptionMaterials;
import software.amazon.cryptography.materialProviders.model.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.MaterialProvidersConfig;
import software.amazon.cryptography.materialProviders.model.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialProviders.model.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnEncryptInput;

public class MaterialProviders {
  private final IAwsCryptographicMaterialProvidersClient _impl;

  protected MaterialProviders(BuilderImpl builder) {
    MaterialProvidersConfig nativeValue = builder.MaterialProvidersConfig();
    Dafny.Aws.Cryptography.MaterialProviders.Types.MaterialProvidersConfig dafnyValue = ToDafny.MaterialProvidersConfig(nativeValue);
    Result<MaterialProvidersClient, Error> result = __default.MaterialProviders(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Keyring CreateAwsKmsKeyring(CreateAwsKmsKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsKeyringInput dafnyValue = ToDafny.CreateAwsKmsKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsDiscoveryKeyring(CreateAwsKmsDiscoveryKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryKeyringInput dafnyValue = ToDafny.CreateAwsKmsDiscoveryKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsDiscoveryKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsMultiKeyring(CreateAwsKmsMultiKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMultiKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsDiscoveryMultiKeyring(
      CreateAwsKmsDiscoveryMultiKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsDiscoveryMultiKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsDiscoveryMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsMrkKeyring(CreateAwsKmsMrkKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsMrkMultiKeyring(CreateAwsKmsMrkMultiKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkMultiKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsMrkDiscoveryKeyring(
      CreateAwsKmsMrkDiscoveryKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkDiscoveryKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkDiscoveryKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateAwsKmsMrkDiscoveryMultiKeyring(
      CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkDiscoveryMultiKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateMultiKeyring(CreateMultiKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateMultiKeyringInput dafnyValue = ToDafny.CreateMultiKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateRawAesKeyring(CreateRawAesKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawAesKeyringInput dafnyValue = ToDafny.CreateRawAesKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateRawAesKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public Keyring CreateRawRsaKeyring(CreateRawRsaKeyringInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawRsaKeyringInput dafnyValue = ToDafny.CreateRawRsaKeyringInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Error> result = this._impl.CreateRawRsaKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.create(result.dtor_value());
  }

  public ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
      CreateDefaultCryptographicMaterialsManagerInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultCryptographicMaterialsManagerInput dafnyValue = ToDafny.CreateDefaultCryptographicMaterialsManagerInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager, Error> result = this._impl.CreateDefaultCryptographicMaterialsManager(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return CryptographicMaterialsManager.create(result.dtor_value());
  }

  public IClientSupplier CreateDefaultClientSupplier(CreateDefaultClientSupplierInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultClientSupplierInput dafnyValue = ToDafny.CreateDefaultClientSupplierInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier, Error> result = this._impl.CreateDefaultClientSupplier(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ClientSupplier.create(result.dtor_value());
  }

  public EncryptionMaterials InitializeEncryptionMaterials(
      InitializeEncryptionMaterialsInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeEncryptionMaterialsInput dafnyValue = ToDafny.InitializeEncryptionMaterialsInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptionMaterials, Error> result = this._impl.InitializeEncryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.EncryptionMaterials(result.dtor_value());
  }

  public DecryptionMaterials InitializeDecryptionMaterials(
      InitializeDecryptionMaterialsInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeDecryptionMaterialsInput dafnyValue = ToDafny.InitializeDecryptionMaterialsInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptionMaterials, Error> result = this._impl.InitializeDecryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DecryptionMaterials(result.dtor_value());
  }

  public void ValidEncryptionMaterialsTransition(
      ValidEncryptionMaterialsTransitionInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.ValidEncryptionMaterialsTransitionInput dafnyValue = ToDafny.ValidEncryptionMaterialsTransitionInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidEncryptionMaterialsTransition(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidDecryptionMaterialsTransition(
      ValidDecryptionMaterialsTransitionInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.ValidDecryptionMaterialsTransitionInput dafnyValue = ToDafny.ValidDecryptionMaterialsTransitionInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidDecryptionMaterialsTransition(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void EncryptionMaterialsHasPlaintextDataKey(EncryptionMaterials nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptionMaterials dafnyValue = ToDafny.EncryptionMaterials(nativeValue);
    Result<Tuple0, Error> result = this._impl.EncryptionMaterialsHasPlaintextDataKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void DecryptionMaterialsWithPlaintextDataKey(DecryptionMaterials nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptionMaterials dafnyValue = ToDafny.DecryptionMaterials(nativeValue);
    Result<Tuple0, Error> result = this._impl.DecryptionMaterialsWithPlaintextDataKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public AlgorithmSuiteInfo GetAlgorithmSuiteInfo(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> dafnyValue = ToDafny.GetAlgorithmSuiteInfoInput(nativeValue);
    Result<Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteInfo, Error> result = this._impl.GetAlgorithmSuiteInfo(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.AlgorithmSuiteInfo(result.dtor_value());
  }

  public void ValidAlgorithmSuiteInfo(AlgorithmSuiteInfo nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteInfo dafnyValue = ToDafny.AlgorithmSuiteInfo(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidAlgorithmSuiteInfo(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidateCommitmentPolicyOnEncrypt(
      ValidateCommitmentPolicyOnEncryptInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnEncryptInput dafnyValue = ToDafny.ValidateCommitmentPolicyOnEncryptInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidateCommitmentPolicyOnEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidateCommitmentPolicyOnDecrypt(
      ValidateCommitmentPolicyOnDecryptInput nativeValue) {
    Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnDecryptInput dafnyValue = ToDafny.ValidateCommitmentPolicyOnDecryptInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidateCommitmentPolicyOnDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  protected IAwsCryptographicMaterialProvidersClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder MaterialProvidersConfig(MaterialProvidersConfig MaterialProvidersConfig);

    MaterialProvidersConfig MaterialProvidersConfig();

    MaterialProviders build();
  }

  static class BuilderImpl implements Builder {
    protected MaterialProvidersConfig MaterialProvidersConfig;

    protected BuilderImpl() {
    }

    public Builder MaterialProvidersConfig(MaterialProvidersConfig MaterialProvidersConfig) {
      this.MaterialProvidersConfig = MaterialProvidersConfig;
      return this;
    }

    public MaterialProvidersConfig MaterialProvidersConfig() {
      return this.MaterialProvidersConfig;
    }

    public MaterialProviders build() {
      if (Objects.isNull(this.MaterialProvidersConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `MaterialProvidersConfig`");
      }
      return new MaterialProviders(this);
    }
  }
}
