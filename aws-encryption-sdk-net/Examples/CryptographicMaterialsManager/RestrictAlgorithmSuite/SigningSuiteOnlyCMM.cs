using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using AWS.EncryptionSDK.Core;

/// <summary>
/// Demonstrates creating a custom Cryptographic Materials Manager (CMM).
/// The SigningSuiteOnlyCMM ensures that callers use an Algorithm Suite with
/// signing. This is a best practice. Read more about Digital Signing:
/// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#digital-sigs
/// Read more about Cryptographic Materials Managers (CMMs):
/// https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/concepts.html#crypt-materials-manager
/// </summary>
public class SigningSuiteOnlyCMM : ICryptographicMaterialsManager
{
    private readonly ICryptographicMaterialsManager _cmm;

    private readonly ImmutableHashSet<AlgorithmSuiteId> _approvedAlgos = new HashSet<AlgorithmSuiteId>()
    {
        AlgorithmSuiteId.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256,
        AlgorithmSuiteId.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
        AlgorithmSuiteId.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
        AlgorithmSuiteId.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384
    }.ToImmutableHashSet();

    public SigningSuiteOnlyCMM(IKeyring keyring, IAwsCryptographicMaterialProviders materialProviders)
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

    public GetEncryptionMaterialsOutput GetEncryptionMaterials(GetEncryptionMaterialsInput input)
    {
        if (!_approvedAlgos.Contains(input.AlgorithmSuiteId))
        {
            throw new Exception("Algorithm Suite must use Signing");
        }
        return _cmm.GetEncryptionMaterials(input);
    }

    public DecryptMaterialsOutput DecryptMaterials(DecryptMaterialsInput input)
    {
        if (!_approvedAlgos.Contains(input.AlgorithmSuiteId))
        {
            throw new NonSigningSuiteException();
        }
        return _cmm.DecryptMaterials(input);
    }
}

public class NonSigningSuiteException : Exception
{
    public NonSigningSuiteException() : base("Algorithm Suite must use Signing") { }
}

