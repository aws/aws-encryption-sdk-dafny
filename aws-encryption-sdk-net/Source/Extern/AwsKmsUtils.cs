using Amazon.KeyManagementService;
using Com.Amazonaws.Kms;
using Wrappers_Compile;
namespace AwsKmsUtils
{
    public partial class __default
    {
        public static _IOption<bool> RegionMatch(
            Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient client,
            Dafny.ISequence<char> region)
        {
            string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
            IAmazonKeyManagementService nativeClient =
                AWS.EncryptionSDK.Core.TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S18_KmsClientReference(client);
            return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
        }
    }
}
