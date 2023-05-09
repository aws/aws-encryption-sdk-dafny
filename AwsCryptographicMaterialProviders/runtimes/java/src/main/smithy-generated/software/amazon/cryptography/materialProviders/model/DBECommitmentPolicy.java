// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public enum DBECommitmentPolicy {
  REQUIRE_ENCRYPT_REQUIRE_DECRYPT("REQUIRE_ENCRYPT_REQUIRE_DECRYPT");

  private final String value;

  private DBECommitmentPolicy(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
