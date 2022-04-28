// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using Amazon;
using Amazon.KeyManagementService;
using Amazon.SecurityToken;
using Amazon.SecurityToken.Model;
using AWS.EncryptionSDK.Core;
using static ExampleUtils.ExampleUtils;

/// <summary>
///     Demonstrates implementing a Custom Client Supplier.
///     This Client Supplier will create KMS Clients with different IAM roles,
///     depending on the Region passed.
/// </summary>
// When implementing a Custom Client Supplier ALWAYS extend the Base class,
// not the interface.
public class RegionalRoleClientSupplier : ClientSupplierBase
{
    /// <summary>
    ///     Maps a Region to the Arn of the IAM Role the client supplier will
    ///     use when supplying a client.
    /// </summary>
    private static Dictionary<string, string> _regionIAMRoleMap;

    /// <summary>
    ///     Amazon Security Token Service, or STS, allows customers to fetch
    ///     temporary credentials.
    /// </summary>
    private static IAmazonSecurityTokenService _stsClient;

    public RegionalRoleClientSupplier()
    {
        _regionIAMRoleMap = GetRegionIAMRoleMap();
        _stsClient = new AmazonSecurityTokenServiceClient();
    }

    /// <summary>
    ///     This is the meat of a Client Supplier.
    ///     Whenever the AWS Encryption SDK needs to create a KMS client,
    ///     it will call <c>GetClient</c> for the regions in which it needs to call
    ///     KMS.
    ///     In this example, we utilize a Dictionary
    ///     to map regions to particular IAM Roles.
    ///     We use Amazon Security Token Service to fetch temporary credentials,
    ///     and then provision a Key Management Service (KMS) Client
    ///     with those credentials and the input region.
    /// </summary>
    /// <param name="input"><c>GetClientInput</c> is just the region</param>
    /// <returns>A KMS Client</returns>
    /// <exception cref="MissingRegionException">If the Region requested is missing from the RegionIAMRole Map</exception>
    /// <exception cref="AssumeRoleException">If the Assume Role call fails</exception>
    protected override IAmazonKeyManagementService _GetClient(GetClientInput input)
    {
        // Check our RegionIAMRole map for the provided region.
        // If it is missing, throw a Missing Region Exception.
        if (!_regionIAMRoleMap.ContainsKey(input.Region)) throw new MissingRegionException(input.Region);

        // Otherwise, call Amazon STS to assume the role.
        var iamArn = _regionIAMRoleMap[input.Region];
        var task = _stsClient.AssumeRoleAsync(new AssumeRoleRequest
        {
            RoleArn = iamArn,
            DurationSeconds = 900, // 15 minutes is the minimum value
            RoleSessionName = "ESDK-NET-Custom-Client-Example"
        });
        AssumeRoleResponse response;
        // Await the async response
        try
        {
            response = task.Result;
        }
        catch (Exception e)
        {
            throw new AssumeRoleException(input.Region, iamArn, e);
        }

        // Return a KMS Client with the credentials from STS and the Region.
        return new AmazonKeyManagementServiceClient(
            response.Credentials,
            RegionEndpoint.GetBySystemName(input.Region));
    }
}

// Custom Exceptions SHOULD extend from the Library's Base Exception.
// This is a quirk of using Dafny to generate the Encryption SDK.
// The Encryption SDK will handle dotnet's System.Exception,
// but the exception message will be altered.
// By extending from the Library's Base Exception,
// you can ensure the exception's message will be as intended.
public class MissingRegionException : AwsCryptographicMaterialProvidersBaseException
{
    public MissingRegionException(string region) : base(
        $"Region {region} is not supported by this client supplier")
    {
    }
}

public class AssumeRoleException : AwsCryptographicMaterialProvidersBaseException
{
    public AssumeRoleException(string region, string roleArn, Exception e) : base(
        $"Attempt to assume Role Arn {roleArn} for Region {region}" +
        $" encountered unexpected: {e.GetType()}: \"{e.Message}\"")
    {
        // At this time, the Encryption SDK only retains exception messages,
        // and not the entire stack trace.
        // As such, it is helpful to manually log the exceptions
        // (ideally, a logging framework would be used, instead of console).
        Console.Out.Write(e);
    }
}
