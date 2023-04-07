package Dafny.Aws.Cryptography.MaterialProviders.Wrapped;

import Dafny.Aws.Cryptography.MaterialProviders.Types.Error;
import Dafny.Aws.Cryptography.MaterialProviders.Types.IAwsCryptographicMaterialProvidersClient;
import Dafny.Aws.Cryptography.MaterialProviders.Types.MaterialProvidersConfig;
import Wrappers_Compile.Result;
import software.amazon.cryptography.materialProviders.MaterialProviders;
import software.amazon.cryptography.materialProviders.ToNative;
import software.amazon.cryptography.materialProviders.wrapped.TestMaterialProviders;

public class __default extends _ExternBase___default {
    public static Result<IAwsCryptographicMaterialProvidersClient, Error> WrappedMaterialProviders(MaterialProvidersConfig config) {
        software.amazon.cryptography.materialProviders.model.MaterialProvidersConfig wrappedConfig = ToNative.MaterialProvidersConfig(config);
        software.amazon.cryptography.materialProviders.MaterialProviders impl = MaterialProviders.builder().MaterialProvidersConfig(wrappedConfig).build();
        TestMaterialProviders wrappedClient = TestMaterialProviders.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
