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
// When implementing a Custom Class of any member of AWS.EncryptionSDK.Core,
// ALWAYS extend the Base class, not the interface.
public class CustomClientSupplier : ClientSupplierBase
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

    public CustomClientSupplier()
    {
        _regionIAMRoleMap = GetRegionIAMRoleMap();
        _stsClient = new AmazonSecurityTokenServiceClient();
    }

    /// <summary>
    ///     This is the meat of a Client Supplier.
    ///     The AWS Cryptographic Material Providers library will call
    ///     <c>GetClient</c> for every region an AWS Multi Keyring is passed.
    ///     In this example, we utilize a Dictionary to map regions to particular
    ///     IAM Roles.
    ///     We use Amazon Security Token Service to fetch temporary credentials,
    ///     and then provision a Key Management Service (KMS) Client with those
    ///     credentials and the input region.
    /// </summary>
    /// <param name="input"><c>GetClientInput</c> is just the region</param>
    /// <returns>A KMS Client</returns>
    /// <exception cref="MissingRegionException">If the Region requested is missing from the RegionIAMRole Map</exception>
    /// <exception cref="AssumeRoleException">If the Assume Role call fails</exception>
    // When implementing a method of any member of AWS.EncryptionSDK.Core,
    // ALWAYS extend the abstract method (`_method`).
    // The Base class' concrete method provides input validation, and then invokes
    // the abstract method.
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


public class MissingRegionException : Exception
{
    public MissingRegionException(string region) : base(
        $"Region {region} is not supported by this client supplier")
    {
    }
}

public class AssumeRoleException : Exception
{
    public AssumeRoleException(string region, string roleArn, Exception e) : base(
        $"Attempt to assume Role Arn {roleArn} for Region {region} failed", e)
    {
        // The Encryption SDK, unfortunately, drops details from exceptions.
        // In particular, the stack trace. As such, it is helpful to manually log
        // the exceptions.
        Console.Out.Write(e);
    }
}
