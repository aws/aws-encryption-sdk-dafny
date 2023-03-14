// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProviders;
namespace AWS.Cryptography.MaterialProviders
{
  public interface ICryptographicMaterialsCache
  {
    void PutCacheEntry(AWS.Cryptography.MaterialProviders.PutCacheEntryInput input);
    AWS.Cryptography.MaterialProviders.GetCacheEntryOutput GetCacheEntry(AWS.Cryptography.MaterialProviders.GetCacheEntryInput input);
    void UpdaterUsageMetadata(AWS.Cryptography.MaterialProviders.UpdaterUsageMetadataInput input);
    void DeleteCacheEntry(AWS.Cryptography.MaterialProviders.DeleteCacheEntryInput input);
  }
}
