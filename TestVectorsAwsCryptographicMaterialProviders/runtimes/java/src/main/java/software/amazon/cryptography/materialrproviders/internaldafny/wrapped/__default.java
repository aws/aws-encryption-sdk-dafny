package software.amazon.cryptography.materialproviders.internaldafny.wrapped;

import software.amazon.cryptography.materialproviders.internaldafny.types.Error;
import software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient;
import software.amazon.cryptography.materialproviders.internaldafny.types.MaterialProvidersConfig;
import Wrappers_Compile.Result;
import software.amazon.cryptography.materialproviders.MaterialProviders;
import software.amazon.cryptography.materialproviders.ToNative;
import software.amazon.cryptography.materialproviders.wrapped.TestMaterialProviders;

public class __default extends _ExternBase___default {
    public static Result<IAwsCryptographicMaterialProvidersClient, Error> WrappedMaterialProviders(MaterialProvidersConfig config) {
        software.amazon.cryptography.materialproviders.model.MaterialProvidersConfig wrappedConfig = ToNative.MaterialProvidersConfig(config);
        software.amazon.cryptography.materialproviders.MaterialProviders impl = MaterialProviders.builder().MaterialProvidersConfig(wrappedConfig).build();
        TestMaterialProviders wrappedClient = TestMaterialProviders.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
