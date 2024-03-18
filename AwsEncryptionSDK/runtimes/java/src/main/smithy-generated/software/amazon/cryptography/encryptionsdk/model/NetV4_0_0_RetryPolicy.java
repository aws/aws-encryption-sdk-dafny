// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

/**
 * During Decryption, Allow or Forbid ESDK-NET v4.0.0 Behavior if the ESDK Message Header fails the Header Authentication check.
 */
public enum NetV4_0_0_RetryPolicy {
  FORBID_RETRY("FORBID_RETRY"),

  ALLOW_RETRY("ALLOW_RETRY");

  private final String value;

  private NetV4_0_0_RetryPolicy(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
