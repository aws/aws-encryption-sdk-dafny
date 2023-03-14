// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import software.amazon.cryptography.materialProviders.model.DeleteCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialProviders.model.PutCacheEntryInput;
import software.amazon.cryptography.materialProviders.model.UpdaterUsageMetadataInput;

public interface ICryptographicMaterialsCache {
  void PutCacheEntry(PutCacheEntryInput nativeValue);

  GetCacheEntryOutput GetCacheEntry(GetCacheEntryInput nativeValue);

  void UpdaterUsageMetadata(UpdaterUsageMetadataInput nativeValue);

  void DeleteCacheEntry(DeleteCacheEntryInput nativeValue);
}
