// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using System.IO;
using System.Collections.Generic;
using AWS.Cryptography.MaterialProviders;
using Dafny.Aws.Cryptography.MaterialProviders.Types;
namespace AWS.Cryptography.MaterialProviders
{
  internal class CryptographicMaterialsManager : CryptographicMaterialsManagerBase
  {
    internal readonly Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager _impl;
    internal CryptographicMaterialsManager(Dafny.Aws.Cryptography.MaterialProviders.Types.ICryptographicMaterialsManager impl) { this._impl = impl; }
    protected override AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsOutput _GetEncryptionMaterials(AWS.Cryptography.MaterialProviders.GetEncryptionMaterialsInput input)
    {
      Dafny.Aws.Cryptography.MaterialProviders.Types._IGetEncryptionMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_GetEncryptionMaterialsInput(input);
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IGetEncryptionMaterialsOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = this._impl.GetEncryptionMaterials(internalInput);
      if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
      return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S28_GetEncryptionMaterialsOutput(result.dtor_value);
    }
    protected override AWS.Cryptography.MaterialProviders.DecryptMaterialsOutput _DecryptMaterials(AWS.Cryptography.MaterialProviders.DecryptMaterialsInput input)
    {
      Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptMaterialsInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S21_DecryptMaterialsInput(input);
      Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IDecryptMaterialsOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> result = this._impl.DecryptMaterials(internalInput);
      if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
      return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S22_DecryptMaterialsOutput(result.dtor_value);
    }
  }
}
