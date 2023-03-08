// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.cryptography.materialProviders.model.GetClientInput;

public interface IClientSupplier {
  KmsClient GetClient(GetClientInput nativeValue);
}
