// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic; namespace Com.Amazonaws.Kms {
 public class KeyManagementServiceShim : software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient {
 public Amazon.KeyManagementService.AmazonKeyManagementServiceClient _impl;
 public KeyManagementServiceShim(Amazon.KeyManagementService.AmazonKeyManagementServiceClient impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CancelKeyDeletion(software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest request) {
 Amazon.KeyManagementService.Model.CancelKeyDeletionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_CancelKeyDeletionRequest(request); try {
 Amazon.KeyManagementService.Model.CancelKeyDeletionResponse sdkResponse =
 this._impl.CancelKeyDeletionAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_CancelKeyDeletionResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ConnectCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest request) {
 Amazon.KeyManagementService.Model.ConnectCustomKeyStoreRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S28_ConnectCustomKeyStoreRequest(request); try {
 Amazon.KeyManagementService.Model.ConnectCustomKeyStoreResponse sdkResponse =
 this._impl.ConnectCustomKeyStoreAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S29_ConnectCustomKeyStoreResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateAlias(software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest request) {
 Amazon.KeyManagementService.Model.CreateAliasRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateAliasRequest(request); try {

 this._impl.CreateAliasAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest request) {
 Amazon.KeyManagementService.Model.CreateCustomKeyStoreRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_CreateCustomKeyStoreRequest(request); try {
 Amazon.KeyManagementService.Model.CreateCustomKeyStoreResponse sdkResponse =
 this._impl.CreateCustomKeyStoreAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_CreateCustomKeyStoreResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateGrant(software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest request) {
 Amazon.KeyManagementService.Model.CreateGrantRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_CreateGrantRequest(request); try {
 Amazon.KeyManagementService.Model.CreateGrantResponse sdkResponse =
 this._impl.CreateGrantAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_CreateGrantResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateKey(software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest request) {
 Amazon.KeyManagementService.Model.CreateKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_CreateKeyRequest(request); try {
 Amazon.KeyManagementService.Model.CreateKeyResponse sdkResponse =
 this._impl.CreateKeyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_CreateKeyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Decrypt(software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest request) {
 Amazon.KeyManagementService.Model.DecryptRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_DecryptRequest(request); try {
 Amazon.KeyManagementService.Model.DecryptResponse sdkResponse =
 this._impl.DecryptAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_DecryptResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteAlias(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest request) {
 Amazon.KeyManagementService.Model.DeleteAliasRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DeleteAliasRequest(request); try {

 this._impl.DeleteAliasAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest request) {
 Amazon.KeyManagementService.Model.DeleteCustomKeyStoreRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_DeleteCustomKeyStoreRequest(request); try {
 Amazon.KeyManagementService.Model.DeleteCustomKeyStoreResponse sdkResponse =
 this._impl.DeleteCustomKeyStoreAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_DeleteCustomKeyStoreResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteImportedKeyMaterial(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest request) {
 Amazon.KeyManagementService.Model.DeleteImportedKeyMaterialRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S32_DeleteImportedKeyMaterialRequest(request); try {

 this._impl.DeleteImportedKeyMaterialAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DescribeCustomKeyStores(software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest request) {
 Amazon.KeyManagementService.Model.DescribeCustomKeyStoresRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S30_DescribeCustomKeyStoresRequest(request); try {
 Amazon.KeyManagementService.Model.DescribeCustomKeyStoresResponse sdkResponse =
 this._impl.DescribeCustomKeyStoresAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S31_DescribeCustomKeyStoresResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DescribeKey(software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest request) {
 Amazon.KeyManagementService.Model.DescribeKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_DescribeKeyRequest(request); try {
 Amazon.KeyManagementService.Model.DescribeKeyResponse sdkResponse =
 this._impl.DescribeKeyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_DescribeKeyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisableKey(software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest request) {
 Amazon.KeyManagementService.Model.DisableKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_DisableKeyRequest(request); try {

 this._impl.DisableKeyAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisableKeyRotation(software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest request) {
 Amazon.KeyManagementService.Model.DisableKeyRotationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S25_DisableKeyRotationRequest(request); try {

 this._impl.DisableKeyRotationAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisconnectCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest request) {
 Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S31_DisconnectCustomKeyStoreRequest(request); try {
 Amazon.KeyManagementService.Model.DisconnectCustomKeyStoreResponse sdkResponse =
 this._impl.DisconnectCustomKeyStoreAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S32_DisconnectCustomKeyStoreResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> EnableKey(software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest request) {
 Amazon.KeyManagementService.Model.EnableKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_EnableKeyRequest(request); try {

 this._impl.EnableKeyAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> EnableKeyRotation(software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest request) {
 Amazon.KeyManagementService.Model.EnableKeyRotationRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_EnableKeyRotationRequest(request); try {

 this._impl.EnableKeyRotationAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Encrypt(software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest request) {
 Amazon.KeyManagementService.Model.EncryptRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S14_EncryptRequest(request); try {
 Amazon.KeyManagementService.Model.EncryptResponse sdkResponse =
 this._impl.EncryptAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S15_EncryptResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKey(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest request) {
 Amazon.KeyManagementService.Model.GenerateDataKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateDataKeyRequest(request); try {
 Amazon.KeyManagementService.Model.GenerateDataKeyResponse sdkResponse =
 this._impl.GenerateDataKeyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_GenerateDataKeyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyPair(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest request) {
 Amazon.KeyManagementService.Model.GenerateDataKeyPairRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_GenerateDataKeyPairRequest(request); try {
 Amazon.KeyManagementService.Model.GenerateDataKeyPairResponse sdkResponse =
 this._impl.GenerateDataKeyPairAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_GenerateDataKeyPairResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyPairWithoutPlaintext(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest request) {
 Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S42_GenerateDataKeyPairWithoutPlaintextRequest(request); try {
 Amazon.KeyManagementService.Model.GenerateDataKeyPairWithoutPlaintextResponse sdkResponse =
 this._impl.GenerateDataKeyPairWithoutPlaintextAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S43_GenerateDataKeyPairWithoutPlaintextResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyWithoutPlaintext(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest request) {
 Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S38_GenerateDataKeyWithoutPlaintextRequest(request); try {
 Amazon.KeyManagementService.Model.GenerateDataKeyWithoutPlaintextResponse sdkResponse =
 this._impl.GenerateDataKeyWithoutPlaintextAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S39_GenerateDataKeyWithoutPlaintextResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateRandom(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest request) {
 Amazon.KeyManagementService.Model.GenerateRandomRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S21_GenerateRandomRequest(request); try {
 Amazon.KeyManagementService.Model.GenerateRandomResponse sdkResponse =
 this._impl.GenerateRandomAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S22_GenerateRandomResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetKeyPolicy(software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest request) {
 Amazon.KeyManagementService.Model.GetKeyPolicyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetKeyPolicyRequest(request); try {
 Amazon.KeyManagementService.Model.GetKeyPolicyResponse sdkResponse =
 this._impl.GetKeyPolicyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetKeyPolicyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetKeyRotationStatus(software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest request) {
 Amazon.KeyManagementService.Model.GetKeyRotationStatusRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_GetKeyRotationStatusRequest(request); try {
 Amazon.KeyManagementService.Model.GetKeyRotationStatusResponse sdkResponse =
 this._impl.GetKeyRotationStatusAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_GetKeyRotationStatusResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetParametersForImport(software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest request) {
 Amazon.KeyManagementService.Model.GetParametersForImportRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S29_GetParametersForImportRequest(request); try {
 Amazon.KeyManagementService.Model.GetParametersForImportResponse sdkResponse =
 this._impl.GetParametersForImportAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S30_GetParametersForImportResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetPublicKey(software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest request) {
 Amazon.KeyManagementService.Model.GetPublicKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_GetPublicKeyRequest(request); try {
 Amazon.KeyManagementService.Model.GetPublicKeyResponse sdkResponse =
 this._impl.GetPublicKeyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_GetPublicKeyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ImportKeyMaterial(software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest request) {
 Amazon.KeyManagementService.Model.ImportKeyMaterialRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S24_ImportKeyMaterialRequest(request); try {
 Amazon.KeyManagementService.Model.ImportKeyMaterialResponse sdkResponse =
 this._impl.ImportKeyMaterialAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S25_ImportKeyMaterialResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListAliases(software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest request) {
 Amazon.KeyManagementService.Model.ListAliasesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_ListAliasesRequest(request); try {
 Amazon.KeyManagementService.Model.ListAliasesResponse sdkResponse =
 this._impl.ListAliasesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S19_ListAliasesResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListGrants(software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest request) {
 Amazon.KeyManagementService.Model.ListGrantsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S17_ListGrantsRequest(request); try {
 Amazon.KeyManagementService.Model.ListGrantsResponse sdkResponse =
 this._impl.ListGrantsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S18_ListGrantsResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListKeyPolicies(software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest request) {
 Amazon.KeyManagementService.Model.ListKeyPoliciesRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S22_ListKeyPoliciesRequest(request); try {
 Amazon.KeyManagementService.Model.ListKeyPoliciesResponse sdkResponse =
 this._impl.ListKeyPoliciesAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S23_ListKeyPoliciesResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListResourceTags(software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest request) {
 Amazon.KeyManagementService.Model.ListResourceTagsRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S23_ListResourceTagsRequest(request); try {
 Amazon.KeyManagementService.Model.ListResourceTagsResponse sdkResponse =
 this._impl.ListResourceTagsAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S24_ListResourceTagsResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> PutKeyPolicy(software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest request) {
 Amazon.KeyManagementService.Model.PutKeyPolicyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_PutKeyPolicyRequest(request); try {

 this._impl.PutKeyPolicyAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ReEncrypt(software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest request) {
 Amazon.KeyManagementService.Model.ReEncryptRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S16_ReEncryptRequest(request); try {
 Amazon.KeyManagementService.Model.ReEncryptResponse sdkResponse =
 this._impl.ReEncryptAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S17_ReEncryptResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ReplicateKey(software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest request) {
 Amazon.KeyManagementService.Model.ReplicateKeyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S19_ReplicateKeyRequest(request); try {
 Amazon.KeyManagementService.Model.ReplicateKeyResponse sdkResponse =
 this._impl.ReplicateKeyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S20_ReplicateKeyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> RetireGrant(software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest request) {
 Amazon.KeyManagementService.Model.RetireGrantRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RetireGrantRequest(request); try {

 this._impl.RetireGrantAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> RevokeGrant(software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest request) {
 Amazon.KeyManagementService.Model.RevokeGrantRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_RevokeGrantRequest(request); try {

 this._impl.RevokeGrantAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ScheduleKeyDeletion(software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest request) {
 Amazon.KeyManagementService.Model.ScheduleKeyDeletionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_ScheduleKeyDeletionRequest(request); try {
 Amazon.KeyManagementService.Model.ScheduleKeyDeletionResponse sdkResponse =
 this._impl.ScheduleKeyDeletionAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S27_ScheduleKeyDeletionResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Sign(software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest request) {
 Amazon.KeyManagementService.Model.SignRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S11_SignRequest(request); try {
 Amazon.KeyManagementService.Model.SignResponse sdkResponse =
 this._impl.SignAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S12_SignResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> TagResource(software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest request) {
 Amazon.KeyManagementService.Model.TagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_TagResourceRequest(request); try {

 this._impl.TagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UntagResource(software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest request) {
 Amazon.KeyManagementService.Model.UntagResourceRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S20_UntagResourceRequest(request); try {

 this._impl.UntagResourceAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateAlias(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest request) {
 Amazon.KeyManagementService.Model.UpdateAliasRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S18_UpdateAliasRequest(request); try {

 this._impl.UpdateAliasAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest request) {
 Amazon.KeyManagementService.Model.UpdateCustomKeyStoreRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateCustomKeyStoreRequest(request); try {
 Amazon.KeyManagementService.Model.UpdateCustomKeyStoreResponse sdkResponse =
 this._impl.UpdateCustomKeyStoreAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S28_UpdateCustomKeyStoreResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateKeyDescription(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest request) {
 Amazon.KeyManagementService.Model.UpdateKeyDescriptionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S27_UpdateKeyDescriptionRequest(request); try {

 this._impl.UpdateKeyDescriptionAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdatePrimaryRegion(software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest request) {
 Amazon.KeyManagementService.Model.UpdatePrimaryRegionRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S26_UpdatePrimaryRegionRequest(request); try {

 this._impl.UpdatePrimaryRegionAsync(sdkRequest).Wait();
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Verify(software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest request) {
 Amazon.KeyManagementService.Model.VerifyRequest sdkRequest = TypeConversion.FromDafny_N3_com__N9_amazonaws__N3_kms__S13_VerifyRequest(request); try {
 Amazon.KeyManagementService.Model.VerifyResponse sdkResponse =
 this._impl.VerifyAsync(sdkRequest).Result;
 return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_com__N9_amazonaws__N3_kms__S14_VerifyResponse(sdkResponse));
} catch (System.AggregateException aggregate) when (aggregate.InnerException is Amazon.KeyManagementService.AmazonKeyManagementServiceException ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
}

}
}
}
