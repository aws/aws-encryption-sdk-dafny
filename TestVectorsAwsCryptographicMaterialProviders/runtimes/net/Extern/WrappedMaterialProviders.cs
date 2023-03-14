using Wrappers_Compile;

namespace Dafny.Aws.Cryptography.MaterialProviders.Wrapped
{
  public partial class __default
  {
    public static
      _IResult<
        Types.IAwsCryptographicMaterialProvidersClient,
        Types._IError
      >
      WrappedMaterialProviders(
        Types._IMaterialProvidersConfig config
      )
    {
      var wrappedConfig = AWS.Cryptography.MaterialProviders.Wrapped.TypeConversion
        .FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S23_MaterialProvidersConfig(config);
      var impl = new AWS.Cryptography.MaterialProviders.MaterialProviders(wrappedConfig);
      var wrappedClient = new AWS.Cryptography.MaterialProviders.Wrapped.AwsCryptographicMaterialProvidersShim(impl);

      return Result<
          Types.IAwsCryptographicMaterialProvidersClient,
          Types._IError
        >
        .create_Success(wrappedClient);
    }

    static void Main(string[] args)
    {
      WrappedMaterialProvidersMain_Compile.__default.CheckKeyrings();
    }
  }
}  