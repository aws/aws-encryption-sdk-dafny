// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Amazon.KeyManagementService;
using Amazon;
using Amazon.Runtime;
using Aws.EncryptionSdk.Core;

using Wrappers_Compile;

namespace DefaultClientSupplier {

    public partial class DefaultClientSupplier {
        public _IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient, Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> GetClient(Dafny.Aws.EncryptionSdk.Core._IGetClientInput input)
        {
            try
            {
                GetClientInput convertedInput = TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(input);
                IAmazonKeyManagementService client;
                if (convertedInput.Region != "")
                {
                    var regionEndpoint = RegionEndpoint.GetBySystemName(convertedInput.Region);
                    client = new AmazonKeyManagementServiceClient(regionEndpoint);
                }
                else
                {
                    client = new AmazonKeyManagementServiceClient();
                }

                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Success(
                    TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(client)
                );
            }
            catch (AmazonServiceException e)
            {
                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                    TypeConversion.ToDafny_CommonError_AwsCryptographicMaterialProvidersBaseException(new AwsCryptographicMaterialProvidersException(e.Message))
                );
            }

        }
    }
}
