using Wrappers_Compile;

namespace software.amazon.cryptography.materialproviders.internaldafny.wrapped
{
  public partial class __default
  {
    public static
      _IResult<
        types.IAwsCryptographicMaterialProvidersClient,
        types._IError
      >
      WrappedMaterialProviders(
        types._IMaterialProvidersConfig config
      )
    {
      var wrappedConfig = AWS.Cryptography.MaterialProviders.Wrapped.TypeConversion
        .FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_MaterialProvidersConfig(config);
      var impl = new AWS.Cryptography.MaterialProviders.MaterialProviders(wrappedConfig);
      var wrappedClient = new AWS.Cryptography.MaterialProviders.Wrapped.AwsCryptographicMaterialProvidersShim(impl);

      return Result<
          types.IAwsCryptographicMaterialProvidersClient,
          types._IError
        >
        .create_Success(wrappedClient);
    }

    static void Main(string[] args)
    {
      WrappedMaterialProvidersMain_Compile.__default.CheckKeyrings();
    }
  }
}
