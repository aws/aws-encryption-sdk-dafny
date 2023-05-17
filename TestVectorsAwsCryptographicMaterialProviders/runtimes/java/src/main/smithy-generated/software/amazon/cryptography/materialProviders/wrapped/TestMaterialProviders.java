// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.wrapped;

import Wrappers_Compile.Result;
import dafny.DafnySequence;
import dafny.Tuple0;
import java.lang.Byte;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.MaterialProviders;
import software.amazon.cryptography.materialproviders.ToDafny;
import software.amazon.cryptography.materialproviders.ToNative;
import software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateCryptographicMaterialsCacheInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateExpectedEncryptionContextCMMInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials;
import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient;
import software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier;
import software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache;
import software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring;
import software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidDecryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidEncryptionMaterialsTransitionInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnDecryptInput;
import software.amazon.cryptography.materialproviders.internaldafny.types.ValidateCommitmentPolicyOnEncryptInput;

public class TestMaterialProviders implements IAwsCryptographicMaterialProvidersClient {
  private final MaterialProviders _impl;

  protected TestMaterialProviders(BuilderImpl builder) {
    this._impl = builder.impl();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Result<IKeyring, Error> CreateAwsKmsDiscoveryKeyring(
      CreateAwsKmsDiscoveryKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryKeyringInput nativeInput = ToNative.CreateAwsKmsDiscoveryKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsDiscoveryKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsDiscoveryMultiKeyring(
      CreateAwsKmsDiscoveryMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsDiscoveryMultiKeyringInput nativeInput = ToNative.CreateAwsKmsDiscoveryMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsDiscoveryMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsHierarchicalKeyring(
      CreateAwsKmsHierarchicalKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsHierarchicalKeyringInput nativeInput = ToNative.CreateAwsKmsHierarchicalKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsHierarchicalKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsKeyring(CreateAwsKmsKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsKeyringInput nativeInput = ToNative.CreateAwsKmsKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkDiscoveryKeyring(
      CreateAwsKmsMrkDiscoveryKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryKeyringInput nativeInput = ToNative.CreateAwsKmsMrkDiscoveryKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkDiscoveryKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkDiscoveryMultiKeyring(
      CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMrkDiscoveryMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkKeyring(CreateAwsKmsMrkKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkKeyringInput nativeInput = ToNative.CreateAwsKmsMrkKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkMultiKeyring(
      CreateAwsKmsMrkMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsMrkMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMrkMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMultiKeyring(
      CreateAwsKmsMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsRsaKeyring(CreateAwsKmsRsaKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateAwsKmsRsaKeyringInput nativeInput = ToNative.CreateAwsKmsRsaKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateAwsKmsRsaKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<ICryptographicMaterialsCache, Error> CreateCryptographicMaterialsCache(
      CreateCryptographicMaterialsCacheInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateCryptographicMaterialsCacheInput nativeInput = ToNative.CreateCryptographicMaterialsCacheInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.ICryptographicMaterialsCache nativeOutput = this._impl.CreateCryptographicMaterialsCache(nativeInput);
      ICryptographicMaterialsCache dafnyOutput = ToDafny.CryptographicMaterialsCache(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IClientSupplier, Error> CreateDefaultClientSupplier(
      CreateDefaultClientSupplierInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateDefaultClientSupplierInput nativeInput = ToNative.CreateDefaultClientSupplierInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IClientSupplier nativeOutput = this._impl.CreateDefaultClientSupplier(nativeInput);
      IClientSupplier dafnyOutput = ToDafny.ClientSupplier(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<ICryptographicMaterialsManager, Error> CreateDefaultCryptographicMaterialsManager(
      CreateDefaultCryptographicMaterialsManagerInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateDefaultCryptographicMaterialsManagerInput nativeInput = ToNative.CreateDefaultCryptographicMaterialsManagerInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager nativeOutput = this._impl.CreateDefaultCryptographicMaterialsManager(nativeInput);
      ICryptographicMaterialsManager dafnyOutput = ToDafny.CryptographicMaterialsManager(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<ICryptographicMaterialsManager, Error> CreateExpectedEncryptionContextCMM(
      CreateExpectedEncryptionContextCMMInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateExpectedEncryptionContextCMMInput nativeInput = ToNative.CreateExpectedEncryptionContextCMMInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager nativeOutput = this._impl.CreateExpectedEncryptionContextCMM(nativeInput);
      ICryptographicMaterialsManager dafnyOutput = ToDafny.CryptographicMaterialsManager(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateMultiKeyring(CreateMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateMultiKeyringInput nativeInput = ToNative.CreateMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateRawAesKeyring(CreateRawAesKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateRawAesKeyringInput nativeInput = ToNative.CreateRawAesKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateRawAesKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<IKeyring, Error> CreateRawRsaKeyring(CreateRawRsaKeyringInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.CreateRawRsaKeyringInput nativeInput = ToNative.CreateRawRsaKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.IKeyring nativeOutput = this._impl.CreateRawRsaKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> DecryptionMaterialsWithPlaintextDataKey(
      DecryptionMaterials dafnyInput) {
    software.amazon.cryptography.materialproviders.model.DecryptionMaterials nativeInput = ToNative.DecryptionMaterials(dafnyInput);
    try {
      this._impl.DecryptionMaterialsWithPlaintextDataKey(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> EncryptionMaterialsHasPlaintextDataKey(
      EncryptionMaterials dafnyInput) {
    software.amazon.cryptography.materialproviders.model.EncryptionMaterials nativeInput = ToNative.EncryptionMaterials(dafnyInput);
    try {
      this._impl.EncryptionMaterialsHasPlaintextDataKey(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<AlgorithmSuiteInfo, Error> GetAlgorithmSuiteInfo(
      DafnySequence<? extends Byte> dafnyInput) {
    ByteBuffer nativeInput = software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.model.AlgorithmSuiteInfo nativeOutput = this._impl.GetAlgorithmSuiteInfo(nativeInput);
      AlgorithmSuiteInfo dafnyOutput = ToDafny.AlgorithmSuiteInfo(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<DecryptionMaterials, Error> InitializeDecryptionMaterials(
      InitializeDecryptionMaterialsInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.InitializeDecryptionMaterialsInput nativeInput = ToNative.InitializeDecryptionMaterialsInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.model.DecryptionMaterials nativeOutput = this._impl.InitializeDecryptionMaterials(nativeInput);
      DecryptionMaterials dafnyOutput = ToDafny.DecryptionMaterials(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<EncryptionMaterials, Error> InitializeEncryptionMaterials(
      InitializeEncryptionMaterialsInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.InitializeEncryptionMaterialsInput nativeInput = ToNative.InitializeEncryptionMaterialsInput(dafnyInput);
    try {
      software.amazon.cryptography.materialproviders.model.EncryptionMaterials nativeOutput = this._impl.InitializeEncryptionMaterials(nativeInput);
      EncryptionMaterials dafnyOutput = ToDafny.EncryptionMaterials(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> ValidAlgorithmSuiteInfo(AlgorithmSuiteInfo dafnyInput) {
    software.amazon.cryptography.materialproviders.model.AlgorithmSuiteInfo nativeInput = ToNative.AlgorithmSuiteInfo(dafnyInput);
    try {
      this._impl.ValidAlgorithmSuiteInfo(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> ValidateCommitmentPolicyOnDecrypt(
      ValidateCommitmentPolicyOnDecryptInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnDecryptInput nativeInput = ToNative.ValidateCommitmentPolicyOnDecryptInput(dafnyInput);
    try {
      this._impl.ValidateCommitmentPolicyOnDecrypt(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> ValidateCommitmentPolicyOnEncrypt(
      ValidateCommitmentPolicyOnEncryptInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.ValidateCommitmentPolicyOnEncryptInput nativeInput = ToNative.ValidateCommitmentPolicyOnEncryptInput(dafnyInput);
    try {
      this._impl.ValidateCommitmentPolicyOnEncrypt(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> ValidDecryptionMaterialsTransition(
      ValidDecryptionMaterialsTransitionInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.ValidDecryptionMaterialsTransitionInput nativeInput = ToNative.ValidDecryptionMaterialsTransitionInput(dafnyInput);
    try {
      this._impl.ValidDecryptionMaterialsTransition(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public Result<Tuple0, Error> ValidEncryptionMaterialsTransition(
      ValidEncryptionMaterialsTransitionInput dafnyInput) {
    software.amazon.cryptography.materialproviders.model.ValidEncryptionMaterialsTransitionInput nativeInput = ToNative.ValidEncryptionMaterialsTransitionInput(dafnyInput);
    try {
      this._impl.ValidEncryptionMaterialsTransition(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    }
  }

  public interface Builder {
    Builder impl(MaterialProviders impl);

    MaterialProviders impl();

    TestMaterialProviders build();
  }

  static class BuilderImpl implements Builder {
    protected MaterialProviders impl;

    protected BuilderImpl() {
    }

    public Builder impl(MaterialProviders impl) {
      this.impl = impl;
      return this;
    }

    public MaterialProviders impl() {
      return this.impl;
    }

    public TestMaterialProviders build() {
      if (Objects.isNull(this.impl()))  {
        throw new IllegalArgumentException("Missing value for required field `impl`");
      }
      return new TestMaterialProviders(this);
    }
  }
}
