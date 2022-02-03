// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Amazon.KeyManagementService;
using Amazon;

using Wrappers_Compile;


namespace DefaultClientSupplier {

    public partial class DefaultClientSupplier {
        public _IResult<IAmazonKeyManagementService, Dafny.Aws.Crypto._IAwsCryptographicMaterialProvidersException> GetClient(Dafny.Aws.Crypto._IGetClientInput input)
        {
            if (input.Region != "")
            {
                var regionEndpoint = RegionEndpoint.GetBySystemName(input.Region);
                return new AmazonKeyManagementServiceClient(regionEndpoint);
            }

            return new AmazonKeyManagementServiceClient();
        }
    }
}
