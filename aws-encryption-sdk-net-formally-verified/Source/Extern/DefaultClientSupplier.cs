// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Amazon.KeyManagementService;
using Amazon;
using Aws.Crypto;

using Wrappers_Compile;

namespace DefaultClientSupplier {

    public partial class DefaultClientSupplier {
        public _IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient, Dafny.Aws.Crypto.IAwsCryptographicMaterialProvidersException> GetClient(Dafny.Aws.Crypto._IGetClientInput input)
        {
            GetClientInput convertedInput = TypeConversion.FromDafny_N3_aws__N6_crypto__S14_GetClientInput(input);
            IAmazonKeyManagementService client;
            if (convertedInput.Region != "") {
                var regionEndpoint = RegionEndpoint.GetBySystemName(convertedInput.Region);
                client = new AmazonKeyManagementServiceClient(regionEndpoint);
            } else {
                client = new AmazonKeyManagementServiceClient();
            }
            return TypeConversion.ToDafny_N3_aws__N6_crypto__S18_KmsClientReference(client);
        }
    }
}
