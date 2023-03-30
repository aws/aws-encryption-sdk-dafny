using Amazon;
using Amazon.KeyManagementService;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Kms;

// This extern is identified in Dafny code
// that refines the AWS SDK KMS Model
namespace Dafny.Com.Amazonaws.Kms
{
  public partial class __default
  {
    
    public static
      _IResult<
        Types.IKMSClient,
        Types._IError
      >
      KMSClient()
    {
      // var region = RegionEndpoint.GetBySystemName("us-west-2");
      // TODO add user agent, endpoint, and region
      var client = new AmazonKeyManagementServiceClient();

      return Result<
        Types.IKMSClient,
        Types._IError
      >
        .create_Success(new KeyManagementServiceShim(client));
    }

        public static _IOption<bool> RegionMatch(
            Dafny.Com.Amazonaws.Kms.Types.IKMSClient client,
            Dafny.ISequence<char> region)
        {
            string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
            // We should never be passing anything other than KeyManagementServiceShim as the 'client'.
            // If this cast fails, that indicates that there is something wrong with
            // our code generation.
            IAmazonKeyManagementService nativeClient = ((KeyManagementServiceShim)client)._impl;
            return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
        }    
  }
}
