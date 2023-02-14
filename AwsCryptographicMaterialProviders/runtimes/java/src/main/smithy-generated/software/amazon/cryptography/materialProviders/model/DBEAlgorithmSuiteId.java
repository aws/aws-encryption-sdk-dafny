// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

public enum DBEAlgorithmSuiteId {
  ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384("0x6700"),

  ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384("0x6701");

  private final String value;

  private DBEAlgorithmSuiteId(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
