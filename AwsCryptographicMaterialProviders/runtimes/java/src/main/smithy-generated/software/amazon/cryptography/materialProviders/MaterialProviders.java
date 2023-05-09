// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import Wrappers_Compile.Result;
import dafny.DafnySequence;
import dafny.Tuple0;
import java.lang.Byte;
import java.lang.IllegalArgumentException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient;
import software.amazon.cryptography.materialproviders.internaldafny.__default;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient;
import software.amazon.cryptography.materialproviders.model.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsHierarchicalKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateAwsKmsRsaKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateCryptographicMaterialsCacheInput;
import software.amazon.cryptography.materialproviders.model.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialproviders.model.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialproviders.model.CreateExpectedEncryptionContextCMMInput;
import software.amazon.cryptography.materialproviders.model.CreateMultiKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialproviders.model.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialproviders.model.DecryptionMaterials;
import software.amazon.cryptography.materialproviders.model.EncryptionMaterials;
import software.amazon.cryptography.materialproviders.model.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.model.MaterialProvidersConfig;
import software.amazon.cryptography.materialproviders.model.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.model.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnEncryptInput;

public class MaterialProviders {
  private final IAwsCryptographicMaterialProvidersClient _impl;

  protected MaterialProviders(BuilderImpl builder) {
    MaterialProvidersConfig nativeValue = builder.MaterialProvidersConfig();
    software.amazon.cryptography.materialproviders.internaldafny.types.MaterialProvidersConfig dafnyValue = ToDafny.MaterialProvidersConfig(nativeValue);
    Result<MaterialProvidersClient, Error> result = __default.MaterialProviders(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  MaterialProviders(IAwsCryptographicMaterialProvidersClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public IKeyring CreateAwsKmsDiscoveryKeyring(CreateAwsKmsDiscoveryKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryKeyringInput dafnyValue = ToDafny.CreateAwsKmsDiscoveryKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsDiscoveryKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsDiscoveryMultiKeyring(
      CreateAwsKmsDiscoveryMultiKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsDiscoveryMultiKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsDiscoveryMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsHierarchicalKeyring(
      CreateAwsKmsHierarchicalKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput dafnyValue = ToDafny.CreateAwsKmsHierarchicalKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsHierarchicalKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsKeyring(CreateAwsKmsKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput dafnyValue = ToDafny.CreateAwsKmsKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsMrkDiscoveryKeyring(
      CreateAwsKmsMrkDiscoveryKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkDiscoveryKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkDiscoveryKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsMrkDiscoveryMultiKeyring(
      CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkDiscoveryMultiKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsMrkKeyring(CreateAwsKmsMrkKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsMrkMultiKeyring(CreateAwsKmsMrkMultiKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMrkMultiKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsMrkMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsMultiKeyring(CreateAwsKmsMultiKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMultiKeyringInput dafnyValue = ToDafny.CreateAwsKmsMultiKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateAwsKmsRsaKeyring(CreateAwsKmsRsaKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput dafnyValue = ToDafny.CreateAwsKmsRsaKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateAwsKmsRsaKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public ICryptographicMaterialsCache CreateCryptographicMaterialsCache(
      CreateCryptographicMaterialsCacheInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateCryptographicMaterialsCacheInput dafnyValue = ToDafny.CreateCryptographicMaterialsCacheInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache, Error> result = this._impl.CreateCryptographicMaterialsCache(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return CryptographicMaterialsCache.wrap(result.dtor_value());
  }

  public IClientSupplier CreateDefaultClientSupplier(CreateDefaultClientSupplierInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput dafnyValue = ToDafny.CreateDefaultClientSupplierInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, Error> result = this._impl.CreateDefaultClientSupplier(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ClientSupplier.wrap(result.dtor_value());
  }

  public ICryptographicMaterialsManager CreateDefaultCryptographicMaterialsManager(
      CreateDefaultCryptographicMaterialsManagerInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput dafnyValue = ToDafny.CreateDefaultCryptographicMaterialsManagerInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Error> result = this._impl.CreateDefaultCryptographicMaterialsManager(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return CryptographicMaterialsManager.wrap(result.dtor_value());
  }

  public ICryptographicMaterialsManager CreateExpectedEncryptionContextCMM(
      CreateExpectedEncryptionContextCMMInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateExpectedEncryptionContextCMMInput dafnyValue = ToDafny.CreateExpectedEncryptionContextCMMInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Error> result = this._impl.CreateExpectedEncryptionContextCMM(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return CryptographicMaterialsManager.wrap(result.dtor_value());
  }

  public IKeyring CreateMultiKeyring(CreateMultiKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput dafnyValue = ToDafny.CreateMultiKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateMultiKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateRawAesKeyring(CreateRawAesKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput dafnyValue = ToDafny.CreateRawAesKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateRawAesKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public IKeyring CreateRawRsaKeyring(CreateRawRsaKeyringInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput dafnyValue = ToDafny.CreateRawRsaKeyringInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Error> result = this._impl.CreateRawRsaKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public void DecryptionMaterialsWithPlaintextDataKey(DecryptionMaterials nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials dafnyValue = ToDafny.DecryptionMaterials(nativeValue);
    Result<Tuple0, Error> result = this._impl.DecryptionMaterialsWithPlaintextDataKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void EncryptionMaterialsHasPlaintextDataKey(EncryptionMaterials nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials dafnyValue = ToDafny.EncryptionMaterials(nativeValue);
    Result<Tuple0, Error> result = this._impl.EncryptionMaterialsHasPlaintextDataKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public AlgorithmSuiteInfo GetAlgorithmSuiteInfo(ByteBuffer nativeValue) {
    DafnySequence<? extends Byte> dafnyValue = ToDafny.GetAlgorithmSuiteInfoInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo, Error> result = this._impl.GetAlgorithmSuiteInfo(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.AlgorithmSuiteInfo(result.dtor_value());
  }

  public DecryptionMaterials InitializeDecryptionMaterials(
      InitializeDecryptionMaterialsInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput dafnyValue = ToDafny.InitializeDecryptionMaterialsInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials, Error> result = this._impl.InitializeDecryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.DecryptionMaterials(result.dtor_value());
  }

  public EncryptionMaterials InitializeEncryptionMaterials(
      InitializeEncryptionMaterialsInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput dafnyValue = ToDafny.InitializeEncryptionMaterialsInput(nativeValue);
    Result<software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials, Error> result = this._impl.InitializeEncryptionMaterials(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.EncryptionMaterials(result.dtor_value());
  }

  public void ValidAlgorithmSuiteInfo(AlgorithmSuiteInfo nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo dafnyValue = ToDafny.AlgorithmSuiteInfo(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidAlgorithmSuiteInfo(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidateCommitmentPolicyOnDecrypt(
      ValidateCommitmentPolicyOnDecryptInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnDecryptInput dafnyValue = ToDafny.ValidateCommitmentPolicyOnDecryptInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidateCommitmentPolicyOnDecrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidateCommitmentPolicyOnEncrypt(
      ValidateCommitmentPolicyOnEncryptInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnEncryptInput dafnyValue = ToDafny.ValidateCommitmentPolicyOnEncryptInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidateCommitmentPolicyOnEncrypt(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidDecryptionMaterialsTransition(
      ValidDecryptionMaterialsTransitionInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.ValidDecryptionMaterialsTransitionInput dafnyValue = ToDafny.ValidDecryptionMaterialsTransitionInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidDecryptionMaterialsTransition(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  public void ValidEncryptionMaterialsTransition(
      ValidEncryptionMaterialsTransitionInput nativeValue) {
    software.amazon.cryptography.materialproviders.internaldafny.types.ValidEncryptionMaterialsTransitionInput dafnyValue = ToDafny.ValidEncryptionMaterialsTransitionInput(nativeValue);
    Result<Tuple0, Error> result = this._impl.ValidEncryptionMaterialsTransition(dafnyValue);
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
