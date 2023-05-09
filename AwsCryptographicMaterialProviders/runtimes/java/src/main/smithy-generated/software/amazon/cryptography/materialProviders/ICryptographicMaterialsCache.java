// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import software.amazon.cryptography.materialproviders.model.DeleteCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialproviders.model.PutCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.UpdaterUsageMetadataInput;

public interface ICryptographicMaterialsCache {
  void DeleteCacheEntry(DeleteCacheEntryInput nativeValue);

  GetCacheEntryOutput GetCacheEntry(GetCacheEntryInput nativeValue);

  void PutCacheEntry(PutCacheEntryInput nativeValue);

  void UpdaterUsageMetadata(UpdaterUsageMetadataInput nativeValue);
}
