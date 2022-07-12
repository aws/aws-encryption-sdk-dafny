// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Reflection;
using System.Threading.Tasks;
using Amazon;
using Amazon.KeyManagementService;
using Amazon.Runtime;
using Amazon.Runtime.Internal;
using Amazon.Util;
// ReSharper disable once RedundantUsingDirective
using AWS.EncryptionSDK.Core;

// ReSharper disable once RedundantUsingDirective
using Wrappers_Compile;

namespace DefaultClientSupplier
{
    // ReSharper disable once RedundantExtendsListEntry
    public partial class DefaultClientSupplier : Dafny.Aws.EncryptionSdk.Core.IClientSupplier
    {
        // ReSharper disable once RedundantNameQualifier
        public Wrappers_Compile._IResult<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
            Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException> GetClient(
            Dafny.Aws.EncryptionSdk.Core._IGetClientInput input)
        {
            GetClientInput convertedInput =
                AWS.EncryptionSDK.Core.TypeConversion.FromDafny_N3_aws__N13_encryptionSdk__N4_core__S14_GetClientInput(input);
            try
            {
                var regionEndpoint = string.IsNullOrEmpty(convertedInput.Region)
                    ? null
                    : RegionEndpoint.GetBySystemName(convertedInput.Region);
                var clientConfig = new AmazonKeyManagementServiceConfig
                {
                    RegionEndpoint = regionEndpoint
                };
                var client = new DefaultKmsClient(clientConfig);

                // ReSharper disable once RedundantNameQualifier
                return Wrappers_Compile.Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Success(
                    AWS.EncryptionSDK.Core.TypeConversion.ToDafny_N3_aws__N13_encryptionSdk__N4_core__S15_GetClientOutput__M6_client(client)
                );
            }
            catch (AmazonServiceException e)
            {
                return Result<Dafny.Com.Amazonaws.Kms.IKeyManagementServiceClient,
                    Dafny.Aws.EncryptionSdk.Core.IAwsCryptographicMaterialProvidersException>.create_Failure(
                    AWS.EncryptionSDK.Core.TypeConversion.ToDafny_CommonError(e)
                );
            }
        }
    }

    /// <summary>
    /// A KMS client that adds the Encryption SDK version to the user agent.
    /// </summary>
    internal class DefaultKmsClient : AmazonKeyManagementServiceClient
    {
        public DefaultKmsClient(AmazonKeyManagementServiceConfig config) : base(config)
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
            AssemblyName assembly = typeof(UserAgentHandler).Assembly.GetName();
            string version = $"{assembly.Version.Major}.{assembly.Version.Minor}.{assembly.Version.Build}";
            UserAgentSuffix = $" AwsEncryptionSdkNet/{version}";

            Console.WriteLine(assembly);
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

        protected void AddUserAgent(IExecutionContext executionContext)
        {
            var request = executionContext.RequestContext.Request;
            request.Headers[AWSSDKUtils.UserAgentHeader] += UserAgentSuffix;
        }
    }
}
