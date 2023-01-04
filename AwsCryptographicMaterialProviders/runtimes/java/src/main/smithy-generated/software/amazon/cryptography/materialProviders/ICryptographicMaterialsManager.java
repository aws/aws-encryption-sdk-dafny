// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import software.amazon.cryptography.materialProviders.model.DecryptMaterialsInput;
import software.amazon.cryptography.materialProviders.model.DecryptMaterialsOutput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsInput;
import software.amazon.cryptography.materialProviders.model.GetEncryptionMaterialsOutput;

public interface ICryptographicMaterialsManager {
  GetEncryptionMaterialsOutput GetEncryptionMaterials(GetEncryptionMaterialsInput nativeValue);

  DecryptMaterialsOutput DecryptMaterials(DecryptMaterialsInput nativeValue);
}
