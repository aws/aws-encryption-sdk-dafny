using System.Runtime.Loader;
using Amazon;
using Amazon.KeyManagementService;
using Wrappers_Compile;
using Amazon.Runtime;
using Amazon.Runtime.Internal;
using Amazon.Util;
using System.Threading.Tasks;
using Com.Amazonaws.Kms;

// This extern is identified in Dafny code
// that refines the AWS SDK KMS Model
namespace software.amazon.cryptography.services.kms.internaldafny
{
  public partial class __default
  {
    
    public static
      _IResult<
        types.IKMSClient,
        types._IError
      >
      KMSClient()
    {
      var client = new DefaultKmsClient();

      return Result<
        types.IKMSClient,
        types._IError
      >
        .create_Success(new KeyManagementServiceShim(client));
    }

    public static
      _IResult<
        types.IKMSClient,
        types._IError
      >
      KMSClientForRegion(
        Dafny.ISequence<char> regionDafnyString
      )
    {
      string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(regionDafnyString);
      var region = RegionEndpoint.GetBySystemName(regionStr);
      var client = new DefaultKmsClient(region);

      return Result<
        types.IKMSClient,
        types._IError
      >
        .create_Success(new KeyManagementServiceShim(client));
    }

    public static _IOption<bool> RegionMatch(
        software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient client,
        Dafny.ISequence<char> region
    ) {
        string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
        // We should never be passing anything other than KeyManagementServiceShim as the 'client'.
        // If this cast fails, that indicates that there is something wrong with
        // our code generation.
        IAmazonKeyManagementService nativeClient = ((KeyManagementServiceShim)client)._impl;
        return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
    }
    
    /// <summary>
    /// A KMS client that adds the Encryption SDK version to the user agent.
    /// </summary>
    internal class DefaultKmsClient : AmazonKeyManagementServiceClient
    {
      public DefaultKmsClient(AmazonKeyManagementServiceConfig config) : base(config)
      {
      }
      public DefaultKmsClient() : base()
      {
      }
      
      public DefaultKmsClient(RegionEndpoint region) : base(region)
      {
      }

      protected override void CustomizeRuntimePipeline(RuntimePipeline pipeline)
      {
        base.CustomizeRuntimePipeline(pipeline);
        pipeline.AddHandlerAfter<Marshaller>(new UserAgentHandler());
      }
    }

    /// <summary>
    /// Adds the Encryption SDK version to the user agent.
    /// </summary>
    internal class UserAgentHandler : PipelineHandler
    {
      private static readonly string UserAgentSuffix;

      static UserAgentHandler()
      {
        var runtime = Dafny.Sequence<char>.FromString("Net");
        UserAgentSuffix = new string(DafnyUserAgentSuffix(runtime).CloneAsArray());
      }

      /// <inheritdoc />
      public override void InvokeSync(IExecutionContext executionContext)
      {
        AddUserAgent(executionContext);
        base.InvokeSync(executionContext);
      }

      /// <inheritdoc />
      public override Task<T> InvokeAsync<T>(IExecutionContext executionContext)
      {
        AddUserAgent(executionContext);
        return base.InvokeAsync<T>(executionContext);
      }

      private static void AddUserAgent(IExecutionContext executionContext)
      {
        var request = executionContext.RequestContext.Request;
        request.Headers[AWSSDKUtils.UserAgentHeader] += UserAgentSuffix;
      }
    }
  }
}
