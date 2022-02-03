// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Amazon.KeyManagementService;
using Amazon;

namespace DefaultClientSupplier {

    public partial class DefaultClientSupplier {
        public IAmazonKeyManagementService GetClient(_IGetClientInput input)
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
