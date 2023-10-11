// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using AWS.Cryptography.MaterialProviders;

/// <summary>
/// Demonstrates how to create a BranchKeyIdSupplier.
///
/// The BranchKeyIdSupplier determines which Branch Key is used
/// to protect or access data.
/// It is an important component in a Multi-tenant solution,
/// where each tenant is cryptographically isolated.
/// The Branch Key ID Supplier uses the Encryption Context
/// provided at Encrypt or Decrypt
/// to determine what "shared secret" (Branch Key)
/// is used.
/// </summary>
public class ExampleBranchKeySupplier : BranchKeyIdSupplierBase 
{
    private string branchKeyTenantA;
    private string branchKeyTenantB;
    
    public ExampleBranchKeySupplier(string branchKeyTenantA, string branchKeyTenantB)
    {
        this.branchKeyTenantA = branchKeyTenantA;
        this.branchKeyTenantB = branchKeyTenantB;
    }
    
    // We MUST use the encryption context to determine
    // the Branch Key ID.
    protected override GetBranchKeyIdOutput _GetBranchKeyId(GetBranchKeyIdInput input)
    {
        Dictionary<string, string> encryptionContext = input.EncryptionContext;
        
        if (!encryptionContext.ContainsKey("tenant"))
        {
            throw new Exception("EncryptionContext invalid, does not contain expected tenant key value pair.");
        }

        string tenant = encryptionContext["tenant"];

        if (tenant.Equals("TenantA"))
        {
            GetBranchKeyIdOutput output = new GetBranchKeyIdOutput();
            output.BranchKeyId = branchKeyTenantA;
            return output;
        } 
        if (tenant.Equals("TenantB"))
        {
            GetBranchKeyIdOutput output = new GetBranchKeyIdOutput();
            output.BranchKeyId = branchKeyTenantB;
            return output;
        }

        throw new Exception("Item does not have a valid tenantID.");
    }
}
