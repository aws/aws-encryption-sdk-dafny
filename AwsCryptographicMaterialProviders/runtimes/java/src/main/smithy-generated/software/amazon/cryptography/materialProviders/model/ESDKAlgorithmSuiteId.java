// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public enum ESDKAlgorithmSuiteId {
  ALG_AES_128_GCM_IV12_TAG16_NO_KDF("0x0014"),

  ALG_AES_192_GCM_IV12_TAG16_NO_KDF("0x0046"),

  ALG_AES_256_GCM_IV12_TAG16_NO_KDF("0x0078"),

  ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256("0x0114"),

  ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256("0x0146"),

  ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256("0x0178"),

  ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256("0x0214"),

  ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384("0x0346"),

  ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384("0x0378"),

  ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY("0x0478"),

  ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384("0x0578");

  private final String value;

  private ESDKAlgorithmSuiteId(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
