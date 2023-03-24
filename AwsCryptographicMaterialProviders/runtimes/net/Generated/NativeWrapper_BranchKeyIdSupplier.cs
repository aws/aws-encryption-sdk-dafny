// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// ReSharper disable RedundantUsingDirective
// ReSharper disable RedundantNameQualifier
// ReSharper disable SuggestVarOrType_SimpleTypes
using System;
using _System;
using Wrappers_Compile;

namespace AWS.Cryptography.MaterialProviders
{
  internal class NativeWrapper_BranchKeyIdSupplier : Dafny.Aws.Cryptography.MaterialProviders.Types.IBranchKeyIdSupplier
  {
    internal readonly BranchKeyIdSupplierBase _impl;
    public NativeWrapper_BranchKeyIdSupplier(BranchKeyIdSupplierBase nativeImpl)
    {
      _impl = nativeImpl;
    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> GetBranchKeyId(Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdInput input)
    {
      void validateOutput(AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput nativeOutput)
      {
        try { nativeOutput.Validate(); }
        catch (ArgumentException e)
        {
          var message = $"Output of {_impl}._GetBranchKeyId is invalid. {e.Message}";
          throw new AwsCryptographicMaterialProvidersException(message);
        }
      }
      AWS.Cryptography.MaterialProviders.GetBranchKeyIdInput nativeInput = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_GetBranchKeyIdInput(input);
      try
      {
        AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput nativeOutput = _impl.GetBranchKeyId(nativeInput);
        _ = nativeOutput ?? throw new AwsCryptographicMaterialProvidersException($"{_impl}._GetBranchKeyId returned null, should be {typeof(AWS.Cryptography.MaterialProviders.GetBranchKeyIdOutput)}");
        validateOutput(nativeOutput);
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S20_GetBranchKeyIdOutput(nativeOutput));
      }
      catch (Exception e)
      {
        return Wrappers_Compile.Result<Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
      }
    }
    public Wrappers_Compile._IResult<Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdOutput, Dafny.Aws.Cryptography.MaterialProviders.Types._IError> GetBranchKeyId_k(Dafny.Aws.Cryptography.MaterialProviders.Types._IGetBranchKeyIdInput input)
    {
      throw new AwsCryptographicMaterialProvidersException("Not supported at this time.");
    }
  }
}
