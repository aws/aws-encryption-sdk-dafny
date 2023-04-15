// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.wrapped;

import Dafny.Aws.Cryptography.MaterialProviders.Types.AlgorithmSuiteInfo;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsDiscoveryMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsHierarchicalKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkDiscoveryMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMrkMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateAwsKmsRsaKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateCryptographicMaterialsCacheInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultClientSupplierInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateDefaultCryptographicMaterialsManagerInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateExpectedEncryptionContextCMMInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateMultiKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawAesKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.CreateRawRsaKeyringInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.DecryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.EncryptionMaterials;
import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IAwsCryptographicMaterialProvidersClient;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring;
import Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeDecryptionMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.InitializeEncryptionMaterialsInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidDecryptionMaterialsTransitionInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidEncryptionMaterialsTransitionInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnDecryptInput;
import Dafny.Aws.Cryptography.MaterialProviders.Types.ValidateCommitmentPolicyOnEncryptInput;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import dafny.Tuple0;
import java.lang.Byte;
import java.lang.Exception;
import java.lang.IllegalArgumentException;
import java.nio.ByteBuffer;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.MaterialProviders;
import software.amazon.cryptography.materialProviders.ToDafny;
import software.amazon.cryptography.materialProviders.ToNative;
import software.amazon.cryptography.materialProviders.model.OpaqueError;

public class TestMaterialProviders implements IAwsCryptographicMaterialProvidersClient {
  private final MaterialProviders _impl;

  protected TestMaterialProviders(BuilderImpl builder) {
    this._impl = builder.impl();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Result<IKeyring, Error> CreateAwsKmsKeyring(CreateAwsKmsKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsKeyringInput nativeInput = ToNative.CreateAwsKmsKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsDiscoveryKeyring(
      CreateAwsKmsDiscoveryKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryKeyringInput nativeInput = ToNative.CreateAwsKmsDiscoveryKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsDiscoveryKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMultiKeyring(
      CreateAwsKmsMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsDiscoveryMultiKeyring(
      CreateAwsKmsDiscoveryMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsDiscoveryMultiKeyringInput nativeInput = ToNative.CreateAwsKmsDiscoveryMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsDiscoveryMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkKeyring(CreateAwsKmsMrkKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkKeyringInput nativeInput = ToNative.CreateAwsKmsMrkKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkMultiKeyring(
      CreateAwsKmsMrkMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMrkMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkDiscoveryKeyring(
      CreateAwsKmsMrkDiscoveryKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryKeyringInput nativeInput = ToNative.CreateAwsKmsMrkDiscoveryKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkDiscoveryKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsMrkDiscoveryMultiKeyring(
      CreateAwsKmsMrkDiscoveryMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsMrkDiscoveryMultiKeyringInput nativeInput = ToNative.CreateAwsKmsMrkDiscoveryMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsHierarchicalKeyring(
      CreateAwsKmsHierarchicalKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsHierarchicalKeyringInput nativeInput = ToNative.CreateAwsKmsHierarchicalKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsHierarchicalKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateMultiKeyring(CreateMultiKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateMultiKeyringInput nativeInput = ToNative.CreateMultiKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateMultiKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateRawAesKeyring(CreateRawAesKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateRawAesKeyringInput nativeInput = ToNative.CreateRawAesKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateRawAesKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateRawRsaKeyring(CreateRawRsaKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateRawRsaKeyringInput nativeInput = ToNative.CreateRawRsaKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateRawRsaKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IKeyring, Error> CreateAwsKmsRsaKeyring(CreateAwsKmsRsaKeyringInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateAwsKmsRsaKeyringInput nativeInput = ToNative.CreateAwsKmsRsaKeyringInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IKeyring nativeOutput = this._impl.CreateAwsKmsRsaKeyring(nativeInput);
      IKeyring dafnyOutput = ToDafny.Keyring(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<ICryptographicMaterialsManager, Error> CreateDefaultCryptographicMaterialsManager(
      CreateDefaultCryptographicMaterialsManagerInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateDefaultCryptographicMaterialsManagerInput nativeInput = ToNative.CreateDefaultCryptographicMaterialsManagerInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.ICryptographicMaterialsManager nativeOutput = this._impl.CreateDefaultCryptographicMaterialsManager(nativeInput);
      ICryptographicMaterialsManager dafnyOutput = ToDafny.CryptographicMaterialsManager(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<ICryptographicMaterialsManager, Error> CreateExpectedEncryptionContextCMM(
      CreateExpectedEncryptionContextCMMInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateExpectedEncryptionContextCMMInput nativeInput = ToNative.CreateExpectedEncryptionContextCMMInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.ICryptographicMaterialsManager nativeOutput = this._impl.CreateExpectedEncryptionContextCMM(nativeInput);
      ICryptographicMaterialsManager dafnyOutput = ToDafny.CryptographicMaterialsManager(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<ICryptographicMaterialsCache, Error> CreateCryptographicMaterialsCache(
      CreateCryptographicMaterialsCacheInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateCryptographicMaterialsCacheInput nativeInput = ToNative.CreateCryptographicMaterialsCacheInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.ICryptographicMaterialsCache nativeOutput = this._impl.CreateCryptographicMaterialsCache(nativeInput);
      ICryptographicMaterialsCache dafnyOutput = ToDafny.CryptographicMaterialsCache(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<IClientSupplier, Error> CreateDefaultClientSupplier(
      CreateDefaultClientSupplierInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.CreateDefaultClientSupplierInput nativeInput = ToNative.CreateDefaultClientSupplierInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.IClientSupplier nativeOutput = this._impl.CreateDefaultClientSupplier(nativeInput);
      IClientSupplier dafnyOutput = ToDafny.ClientSupplier(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<EncryptionMaterials, Error> InitializeEncryptionMaterials(
      InitializeEncryptionMaterialsInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.InitializeEncryptionMaterialsInput nativeInput = ToNative.InitializeEncryptionMaterialsInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.model.EncryptionMaterials nativeOutput = this._impl.InitializeEncryptionMaterials(nativeInput);
      EncryptionMaterials dafnyOutput = ToDafny.EncryptionMaterials(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<DecryptionMaterials, Error> InitializeDecryptionMaterials(
      InitializeDecryptionMaterialsInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.InitializeDecryptionMaterialsInput nativeInput = ToNative.InitializeDecryptionMaterialsInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.model.DecryptionMaterials nativeOutput = this._impl.InitializeDecryptionMaterials(nativeInput);
      DecryptionMaterials dafnyOutput = ToDafny.DecryptionMaterials(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> ValidEncryptionMaterialsTransition(
      ValidEncryptionMaterialsTransitionInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.ValidEncryptionMaterialsTransitionInput nativeInput = ToNative.ValidEncryptionMaterialsTransitionInput(dafnyInput);
    try {
      this._impl.ValidEncryptionMaterialsTransition(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> ValidDecryptionMaterialsTransition(
      ValidDecryptionMaterialsTransitionInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.ValidDecryptionMaterialsTransitionInput nativeInput = ToNative.ValidDecryptionMaterialsTransitionInput(dafnyInput);
    try {
      this._impl.ValidDecryptionMaterialsTransition(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> EncryptionMaterialsHasPlaintextDataKey(
      EncryptionMaterials dafnyInput) {
    software.amazon.cryptography.materialProviders.model.EncryptionMaterials nativeInput = ToNative.EncryptionMaterials(dafnyInput);
    try {
      this._impl.EncryptionMaterialsHasPlaintextDataKey(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> DecryptionMaterialsWithPlaintextDataKey(
      DecryptionMaterials dafnyInput) {
    software.amazon.cryptography.materialProviders.model.DecryptionMaterials nativeInput = ToNative.DecryptionMaterials(dafnyInput);
    try {
      this._impl.DecryptionMaterialsWithPlaintextDataKey(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<AlgorithmSuiteInfo, Error> GetAlgorithmSuiteInfo(
      DafnySequence<? extends Byte> dafnyInput) {
    ByteBuffer nativeInput = ToNative.GetAlgorithmSuiteInfoInput(dafnyInput);
    try {
      software.amazon.cryptography.materialProviders.model.AlgorithmSuiteInfo nativeOutput = this._impl.GetAlgorithmSuiteInfo(nativeInput);
      AlgorithmSuiteInfo dafnyOutput = ToDafny.AlgorithmSuiteInfo(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> ValidAlgorithmSuiteInfo(AlgorithmSuiteInfo dafnyInput) {
    software.amazon.cryptography.materialProviders.model.AlgorithmSuiteInfo nativeInput = ToNative.AlgorithmSuiteInfo(dafnyInput);
    try {
      this._impl.ValidAlgorithmSuiteInfo(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> ValidateCommitmentPolicyOnEncrypt(
      ValidateCommitmentPolicyOnEncryptInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnEncryptInput nativeInput = ToNative.ValidateCommitmentPolicyOnEncryptInput(dafnyInput);
    try {
      this._impl.ValidateCommitmentPolicyOnEncrypt(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<Tuple0, Error> ValidateCommitmentPolicyOnDecrypt(
      ValidateCommitmentPolicyOnDecryptInput dafnyInput) {
    software.amazon.cryptography.materialProviders.model.ValidateCommitmentPolicyOnDecryptInput nativeInput = ToNative.ValidateCommitmentPolicyOnDecryptInput(dafnyInput);
    try {
      this._impl.ValidateCommitmentPolicyOnDecrypt(nativeInput);
      return Result.create_Success(Tuple0.create());
    } catch (RuntimeException ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
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
