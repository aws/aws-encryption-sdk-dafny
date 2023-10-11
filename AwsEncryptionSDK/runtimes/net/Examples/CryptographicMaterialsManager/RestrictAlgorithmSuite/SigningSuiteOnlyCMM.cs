// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using AWS.Cryptography.MaterialProviders;

/// <summary>
/// Demonstrates creating a custom Cryptographic Materials Manager (CMM).
/// The SigningSuiteOnlyCMM ensures that callers use an Algorithm Suite with
/// signing. This is a best practice. Read more about Digital Signing:
/// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#digital-sigs
/// Read more about Cryptographic Materials Managers (CMMs):
/// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#crypt-materials-manager
/// </summary>
public class SigningSuiteOnlyCMM : CryptographicMaterialsManagerBase
{
    private readonly ICryptographicMaterialsManager _cmm;

    private readonly ImmutableHashSet<ESDKAlgorithmSuiteId> _approvedAlgos = new HashSet<ESDKAlgorithmSuiteId>()
    {
        ESDKAlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
        ESDKAlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
        ESDKAlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
        ESDKAlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
    }.ToImmutableHashSet();

    public SigningSuiteOnlyCMM(IKeyring keyring, MaterialProviders materialProviders)
    {
        // Create a DefaultCryptographicMaterialsManager to facilitate
        // GetEncryptionMaterials and DecryptionMaterials
        // after this CMM approves the Algorithm Suite.
        var cmmInput = new CreateDefaultCryptographicMaterialsManagerInput
        {
            Keyring = keyring
        };
        _cmm = materialProviders.CreateDefaultCryptographicMaterialsManager(cmmInput);
    }

    protected override GetEncryptionMaterialsOutput _GetEncryptionMaterials(GetEncryptionMaterialsInput input)
    {
        if (!_approvedAlgos.Contains(input.AlgorithmSuiteId.ESDK))
        {
            throw new NonSigningSuiteException();
        }
        return _cmm.GetEncryptionMaterials(input);
    }

    protected override DecryptMaterialsOutput _DecryptMaterials(DecryptMaterialsInput input)
    {
        if (!_approvedAlgos.Contains(input.AlgorithmSuiteId.ESDK))
        {
            throw new NonSigningSuiteException();
        }
        return _cmm.DecryptMaterials(input);
    }
}

// Custom Exceptions SHOULD extend from the Library's Base Exception.
// The Encryption SDK will handle dotnet's System.Exception,
// but the exception message will be altered.
// By extending from the Library's Base Exception,
// you can ensure the exception's message will be as intended.
public class NonSigningSuiteException : AwsCryptographicMaterialProvidersException
{
    public NonSigningSuiteException() : base("Algorithm Suite must use Signing") { }
}

