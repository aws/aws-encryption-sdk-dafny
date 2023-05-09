// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.Collections.Generic;
 using System.IO;
 using System.Linq; namespace AWS.Cryptography.MaterialProviders.Wrapped {
 public class AwsCryptographicMaterialProvidersShim : software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient {
 public AWS.Cryptography.MaterialProviders.MaterialProviders _impl;
 public AwsCryptographicMaterialProvidersShim(AWS.Cryptography.MaterialProviders.MaterialProviders impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateAwsKmsKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsDiscoveryKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsDiscoveryKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateAwsKmsDiscoveryKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsDiscoveryKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMultiKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S29_CreateAwsKmsMultiKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsMultiKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsDiscoveryMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsDiscoveryMultiKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsDiscoveryMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateAwsKmsDiscoveryMultiKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsDiscoveryMultiKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsMrkKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsMrkKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsMrkKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsMrkMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkMultiKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateAwsKmsMrkMultiKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsMrkMultiKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsMrkDiscoveryKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkDiscoveryKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsMrkDiscoveryKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsMrkDiscoveryKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsMrkDiscoveryMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkDiscoveryMultiKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsMrkDiscoveryMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateAwsKmsMrkDiscoveryMultiKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsMrkDiscoveryMultiKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsHierarchicalKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsHierarchicalKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsHierarchicalKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S36_CreateAwsKmsHierarchicalKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsHierarchicalKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateMultiKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateMultiKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_CreateMultiKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateMultiKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawAesKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateRawAesKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawAesKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateRawAesKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawRsaKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateRawRsaKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S24_CreateRawRsaKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateRawRsaKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateAwsKmsRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsRsaKeyringInput request) {
 AWS.Cryptography.MaterialProviders.CreateAwsKmsRsaKeyringInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S27_CreateAwsKmsRsaKeyringInput(request); try {
 AWS.Cryptography.MaterialProviders.IKeyring wrappedResponse =
 this._impl.CreateAwsKmsRsaKeyring(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateDefaultCryptographicMaterialsManager(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateDefaultCryptographicMaterialsManagerInput request) {
 AWS.Cryptography.MaterialProviders.CreateDefaultCryptographicMaterialsManagerInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S47_CreateDefaultCryptographicMaterialsManagerInput(request); try {
 AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager wrappedResponse =
 this._impl.CreateDefaultCryptographicMaterialsManager(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S41_CreateCryptographicMaterialsManagerOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateExpectedEncryptionContextCMM(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateExpectedEncryptionContextCMMInput request) {
 AWS.Cryptography.MaterialProviders.CreateExpectedEncryptionContextCMMInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_CreateExpectedEncryptionContextCMMInput(request); try {
 AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager wrappedResponse =
 this._impl.CreateExpectedEncryptionContextCMM(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S40_CreateExpectedEncryptionContextCMMOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateCryptographicMaterialsCache(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateCryptographicMaterialsCacheInput request) {
 AWS.Cryptography.MaterialProviders.CreateCryptographicMaterialsCacheInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_CreateCryptographicMaterialsCacheInput(request); try {
 AWS.Cryptography.MaterialProviders.ICryptographicMaterialsCache wrappedResponse =
 this._impl.CreateCryptographicMaterialsCache(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_CreateCryptographicMaterialsCacheOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types._ICreateDefaultClientSupplierInput request) {
 AWS.Cryptography.MaterialProviders.CreateDefaultClientSupplierInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S32_CreateDefaultClientSupplierInput(request); try {
 AWS.Cryptography.MaterialProviders.IClientSupplier wrappedResponse =
 this._impl.CreateDefaultClientSupplier(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S33_CreateDefaultClientSupplierOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types._IInitializeEncryptionMaterialsInput request) {
 AWS.Cryptography.MaterialProviders.InitializeEncryptionMaterialsInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeEncryptionMaterialsInput(request); try {
 AWS.Cryptography.MaterialProviders.EncryptionMaterials wrappedResponse =
 this._impl.InitializeEncryptionMaterials(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types._IInitializeDecryptionMaterialsInput request) {
 AWS.Cryptography.MaterialProviders.InitializeDecryptionMaterialsInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S34_InitializeDecryptionMaterialsInput(request); try {
 AWS.Cryptography.MaterialProviders.DecryptionMaterials wrappedResponse =
 this._impl.InitializeDecryptionMaterials(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> ValidEncryptionMaterialsTransition(software.amazon.cryptography.materialproviders.internaldafny.types._IValidEncryptionMaterialsTransitionInput request) {
 AWS.Cryptography.MaterialProviders.ValidEncryptionMaterialsTransitionInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidEncryptionMaterialsTransitionInput(request); try {

 this._impl.ValidEncryptionMaterialsTransition(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> ValidDecryptionMaterialsTransition(software.amazon.cryptography.materialproviders.internaldafny.types._IValidDecryptionMaterialsTransitionInput request) {
 AWS.Cryptography.MaterialProviders.ValidDecryptionMaterialsTransitionInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S39_ValidDecryptionMaterialsTransitionInput(request); try {

 this._impl.ValidDecryptionMaterialsTransition(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> EncryptionMaterialsHasPlaintextDataKey(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials request) {
 AWS.Cryptography.MaterialProviders.EncryptionMaterials unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_EncryptionMaterials(request); try {

 this._impl.EncryptionMaterialsHasPlaintextDataKey(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DecryptionMaterialsWithPlaintextDataKey(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials request) {
 AWS.Cryptography.MaterialProviders.DecryptionMaterials unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_DecryptionMaterials(request); try {

 this._impl.DecryptionMaterialsWithPlaintextDataKey(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetAlgorithmSuiteInfo(Dafny.ISequence<byte> request) {
 System.IO.MemoryStream unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S26_GetAlgorithmSuiteInfoInput(request); try {
 AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo wrappedResponse =
 this._impl.GetAlgorithmSuiteInfo(unWrappedRequest);
 return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(TypeConversion.ToDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> ValidAlgorithmSuiteInfo(software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo request) {
 AWS.Cryptography.MaterialProviders.AlgorithmSuiteInfo unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S18_AlgorithmSuiteInfo(request); try {

 this._impl.ValidAlgorithmSuiteInfo(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> ValidateCommitmentPolicyOnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IValidateCommitmentPolicyOnEncryptInput request) {
 AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnEncryptInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnEncryptInput(request); try {

 this._impl.ValidateCommitmentPolicyOnEncrypt(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> ValidateCommitmentPolicyOnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IValidateCommitmentPolicyOnDecryptInput request) {
 AWS.Cryptography.MaterialProviders.ValidateCommitmentPolicyOnDecryptInput unWrappedRequest = TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S38_ValidateCommitmentPolicyOnDecryptInput(request); try {

 this._impl.ValidateCommitmentPolicyOnDecrypt(unWrappedRequest);
 return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(_System.Tuple0.Default());
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(this.ConvertError(ex));
}

}
 private software.amazon.cryptography.materialproviders.internaldafny.types._IError ConvertError(System.Exception error) {

 switch (error) {
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
 return new software.amazon.cryptography.materialproviders.internaldafny.types.Error_CollectionOfErrors(
     Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IError>
     .FromArray(
         collectionOfErrors.list.Select
             (x => TypeConversion.ToDafny_CommonError(x))
         .ToArray()
     )
 );

 default:
    return new software.amazon.cryptography.materialproviders.internaldafny.types.Error_Opaque(error);

}
}
}
}
