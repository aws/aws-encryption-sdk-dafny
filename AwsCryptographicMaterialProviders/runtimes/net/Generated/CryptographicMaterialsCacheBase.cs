// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public abstract class CryptographicMaterialsCacheBase : ICryptographicMaterialsCache {
 public void PutCacheEntry ( AWS.Cryptography.MaterialProviders.PutCacheEntryInput input )
 {
 input.Validate();  _PutCacheEntry ( input ) ;
}
 protected abstract void _PutCacheEntry ( AWS.Cryptography.MaterialProviders.PutCacheEntryInput input ) ;
 public AWS.Cryptography.MaterialProviders.GetCacheEntryOutput GetCacheEntry ( AWS.Cryptography.MaterialProviders.GetCacheEntryInput input )
 {
 input.Validate(); return _GetCacheEntry ( input ) ;
}
 protected abstract AWS.Cryptography.MaterialProviders.GetCacheEntryOutput _GetCacheEntry ( AWS.Cryptography.MaterialProviders.GetCacheEntryInput input ) ;
 public void UpdaterUsageMetadata ( AWS.Cryptography.MaterialProviders.UpdaterUsageMetadataInput input )
 {
 input.Validate();  _UpdaterUsageMetadata ( input ) ;
}
 protected abstract void _UpdaterUsageMetadata ( AWS.Cryptography.MaterialProviders.UpdaterUsageMetadataInput input ) ;
 public void DeleteCacheEntry ( AWS.Cryptography.MaterialProviders.DeleteCacheEntryInput input )
 {
 input.Validate();  _DeleteCacheEntry ( input ) ;
}
 protected abstract void _DeleteCacheEntry ( AWS.Cryptography.MaterialProviders.DeleteCacheEntryInput input ) ;
}
}
