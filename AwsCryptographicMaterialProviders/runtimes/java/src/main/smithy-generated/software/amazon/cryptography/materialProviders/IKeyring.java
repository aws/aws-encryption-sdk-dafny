// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import software.amazon.cryptography.materialProviders.model.OnDecryptInput;
import software.amazon.cryptography.materialProviders.model.OnDecryptOutput;
import software.amazon.cryptography.materialProviders.model.OnEncryptInput;
import software.amazon.cryptography.materialProviders.model.OnEncryptOutput;

public interface IKeyring {
  OnEncryptOutput OnEncrypt(OnEncryptInput nativeValue);

  OnDecryptOutput OnDecrypt(OnDecryptInput nativeValue);
}
