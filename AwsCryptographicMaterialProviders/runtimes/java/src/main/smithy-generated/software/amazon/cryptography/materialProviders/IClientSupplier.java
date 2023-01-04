// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders;

import com.amazonaws.services.kms.AWSKMS;
import software.amazon.cryptography.materialProviders.model.GetClientInput;

public interface IClientSupplier {
  AWSKMS GetClient(GetClientInput nativeValue);
}
