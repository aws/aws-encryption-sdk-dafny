using Amazon.KeyManagementService;
using Wrappers_Compile;

// This is adding an extern to an existing Dafny namespace
namespace AwsKmsUtils_Compile
{
    public partial class __default
    {
        public static _IOption<bool> RegionMatch(
            Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient client,
            Dafny.ISequence<char> region)
        {
            string regionStr =
                AWS.Cryptography.MaterialProviders.TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
            // TODO Move this to the ComAmazonawsKms project.
            // This is MUCH safer in there.
            IAmazonKeyManagementService nativeClient = (IAmazonKeyManagementService)client;
            return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
        }
    }
}