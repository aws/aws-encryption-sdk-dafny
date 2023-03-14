// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
namespace AWS.Cryptography.MaterialProviders.Wrapped
{
  public class AwsCryptographicMaterialProvidersShim : Dafny.Aws.Cryptography.MaterialProviders.Types.IAwsCryptographicMaterialProvidersClient
  {
    public AWS.Cryptography.MaterialProviders.MaterialProviders _impl;
    public AwsCryptographicMaterialProvidersShim(AWS.Cryptography.MaterialProviders.MaterialProviders impl)
    {
      this._impl = impl;
    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateAwsKmsKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsDiscoveryKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsDiscoveryKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateAwsKmsDiscoveryKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsDiscoveryKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsMultiKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMultiKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S29_CreateAwsKmsMultiKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsMultiKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsDiscoveryMultiKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsDiscoveryMultiKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateAwsKmsDiscoveryMultiKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsDiscoveryMultiKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsMrkKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsMrkKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsMrkKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsMrkMultiKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkMultiKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateAwsKmsMrkMultiKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsMrkMultiKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsMrkDiscoveryKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkDiscoveryKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsMrkDiscoveryKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsMrkDiscoveryKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsMrkDiscoveryMultiKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsMrkDiscoveryMultiKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsHierarchicalKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsHierarchicalKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsHierarchicalKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsHierarchicalKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsHierarchicalKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateMultiKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateMultiKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_CreateMultiKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateMultiKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateRawAesKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateRawAesKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateRawAesKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawAesKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateRawAesKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateRawRsaKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateRawRsaKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateRawRsaKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawRsaKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateRawRsaKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateAwsKmsRsaKeyring(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateAwsKmsRsaKeyringInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateAwsKmsRsaKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsRsaKeyringInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
        this._impl.CreateAwsKmsRsaKeyring(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IKeyring, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateDefaultCryptographicMaterialsManager(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateDefaultCryptographicMaterialsManagerInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateDefaultCryptographicMaterialsManagerInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S47_CreateDefaultCryptographicMaterialsManagerInput(request); try
      {
        AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager wrappedResponse =
        this._impl.CreateDefaultCryptographicMaterialsManager(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateCryptographicMaterialsManagerOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateCryptographicMaterialsCache(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateCryptographicMaterialsCacheInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateCryptographicMaterialsCacheInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateCryptographicMaterialsCacheInput(request); try
      {
        AWS.Cryptography.MaterialProviders.ICryptographicMaterialsCache wrappedResponse =
        this._impl.CreateCryptographicMaterialsCache(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_CreateCryptographicMaterialsCacheOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsCache, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> CreateDefaultClientSupplier(Dafny.Aws.Cryptography.MaterialProviders.Types._ICreateDefaultClientSupplierInput request)
    {
      AWS.Cryptography.MaterialProviders.CreateDefaultClientSupplierInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateDefaultClientSupplierInput(request); try
      {
        AWS.Cryptography.MaterialProviders.IClientSupplier wrappedResponse =
        this._impl.CreateDefaultClientSupplier(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateDefaultClientSupplierOutput(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types.IClientSupplier, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> InitializeEncryptionMaterials(Dafny.Aws.Cryptography.MaterialProviders.Types._IInitializeEncryptionMaterialsInput request)
    {
      AWS.Cryptography.MaterialProviders.InitializeEncryptionMaterialsInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeEncryptionMaterialsInput(request); try
      {
        AWS.Cryptography.MaterialProviders.EncryptionMaterials wrappedResponse =
        this._impl.InitializeEncryptionMaterials(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> InitializeDecryptionMaterials(Dafny.Aws.Cryptography.MaterialProviders.Types._IInitializeDecryptionMaterialsInput request)
    {
      AWS.Cryptography.MaterialProviders.InitializeDecryptionMaterialsInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeDecryptionMaterialsInput(request); try
      {
        AWS.Cryptography.MaterialProviders.DecryptionMaterials wrappedResponse =
        this._impl.InitializeDecryptionMaterials(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> ValidEncryptionMaterialsTransition(Dafny.Aws.Cryptography.MaterialProviders.Types._IValidEncryptionMaterialsTransitionInput request)
    {
      AWS.Cryptography.MaterialProviders.ValidEncryptionMaterialsTransitionInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidEncryptionMaterialsTransitionInput(request); try
      {

        this._impl.ValidEncryptionMaterialsTransition(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> ValidDecryptionMaterialsTransition(Dafny.Aws.Cryptography.MaterialProviders.Types._IValidDecryptionMaterialsTransitionInput request)
    {
      AWS.Cryptography.MaterialProviders.ValidDecryptionMaterialsTransitionInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidDecryptionMaterialsTransitionInput(request); try
      {

        this._impl.ValidDecryptionMaterialsTransition(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> EncryptionMaterialsHasPlaintextDataKey(Dafny.Aws.Cryptography.MaterialProviders.Types._IEncryptionMaterials request)
    {
      AWS.Cryptography.MaterialProviders.EncryptionMaterials unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(request); try
      {

        this._impl.EncryptionMaterialsHasPlaintextDataKey(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> DecryptionMaterialsWithPlaintextDataKey(Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptionMaterials request)
    {
      AWS.Cryptography.MaterialProviders.DecryptionMaterials unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(request); try
      {

        this._impl.DecryptionMaterialsWithPlaintextDataKey(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> GetAlgorithmSuiteInfo(Dafny.ISequence<byte> request)
    {
      System.IO.MemoryStream unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_GetAlgorithmSuiteInfoInput(request); try
      {
        AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo wrappedResponse =
        this._impl.GetAlgorithmSuiteInfo(unWrappedRequest);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(wrappedResponse));
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> ValidAlgorithmSuiteInfo(Dafny.Aws.Cryptography.MaterialProviders.Types._IAlgorithmSuiteInfo request)
    {
      AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(request); try
      {

        this._impl.ValidAlgorithmSuiteInfo(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> ValidateCommitmentPolicyOnEncrypt(Dafny.Aws.Cryptography.MaterialProviders.Types._IValidateCommitmentPolicyOnEncryptInput request)
    {
      AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnEncryptInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnEncryptInput(request); try
      {

        this._impl.ValidateCommitmentPolicyOnEncrypt(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    public Wrappers_Compile._IResult<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> ValidateCommitmentPolicyOnDecrypt(Dafny.Aws.Cryptography.MaterialProviders.Types._IValidateCommitmentPolicyOnDecryptInput request)
    {
      AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnDecryptInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnDecryptInput(request); try
      {

        this._impl.ValidateCommitmentPolicyOnDecrypt(unWrappedRequest);
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(_System.Tuple0.Default());
      }
      catch (System.Exception ex)
      {
        return Wrappers_Compile.Result<_System._ITuple0, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(this.ConvertError(ex));
      }

    }
    private Dafny.Aws.Cryptography.MaterialProviders.Types._IError ConvertError(System.Exception error)
    {

      switch (error)
      {
        case AWS.Cryptography.MaterialProviders.AwsCryptographicMaterialProvidersException e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S42_AwsCryptographicMaterialProvidersException(e);

        case AWS.Cryptography.MaterialProviders.EntryAlreadyExists e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_EntryAlreadyExists(e);

        case AWS.Cryptography.MaterialProviders.EntryDoesNotExist e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S17_EntryDoesNotExist(e);

        case AWS.Cryptography.MaterialProviders.InvalidAlgorithmSuiteInfo e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S25_InvalidAlgorithmSuiteInfo(e);

        case AWS.Cryptography.MaterialProviders.InvalidAlgorithmSuiteInfoOnDecrypt e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InvalidAlgorithmSuiteInfoOnDecrypt(e);

        case AWS.Cryptography.MaterialProviders.InvalidAlgorithmSuiteInfoOnEncrypt e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InvalidAlgorithmSuiteInfoOnEncrypt(e);

        case AWS.Cryptography.MaterialProviders.InvalidDecryptionMaterials e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_InvalidDecryptionMaterials(e);

        case AWS.Cryptography.MaterialProviders.InvalidDecryptionMaterialsTransition e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_InvalidDecryptionMaterialsTransition(e);

        case AWS.Cryptography.MaterialProviders.InvalidEncryptionMaterials e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_InvalidEncryptionMaterials(e);

        case AWS.Cryptography.MaterialProviders.InvalidEncryptionMaterialsTransition e:
          return TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_InvalidEncryptionMaterialsTransition(e);

        case CollectionOfErrors collectionOfErrors:
          return new Dafny.Aws.Cryptography.MaterialProviders.Types.Error_CollectionOfErrors(
              Dafny.Sequence<Dafny.Aws.Cryptography.MaterialProviders.Types._IError>
              .FromArray(
                  collectionOfErrors.list.Select
                      (x => TypeConversion.ToDafny_CommonError(x))
                  .ToArray()
              )
          );

        default:
          return new Dafny.Aws.Cryptography.MaterialProviders.Types.Error_Opaque(error);

      }
    }
  }
}
