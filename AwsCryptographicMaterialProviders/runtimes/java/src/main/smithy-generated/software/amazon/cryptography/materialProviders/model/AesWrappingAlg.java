// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public enum AesWrappingAlg {
  ALG_AES128_GCM_IV12_TAG16("ALG_AES128_GCM_IV12_TAG16"),

  ALG_AES192_GCM_IV12_TAG16("ALG_AES192_GCM_IV12_TAG16"),

  ALG_AES256_GCM_IV12_TAG16("ALG_AES256_GCM_IV12_TAG16");

  private final String value;

  private AesWrappingAlg(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
