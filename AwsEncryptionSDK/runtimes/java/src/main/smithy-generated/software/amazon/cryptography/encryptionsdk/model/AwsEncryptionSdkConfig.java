// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.encryptionsdk.model;

import software.amazon.cryptography.materialproviders.model.ESDKCommitmentPolicy;

public class AwsEncryptionSdkConfig {

  private final ESDKCommitmentPolicy commitmentPolicy;

  private final long maxEncryptedDataKeys;

  /**
   * During Decryption, Allow or Forbid ESDK-NET v4.0.0 Behavior if the ESDK Message Header fails the Header Authentication check.
   */
  private final NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy;

  protected AwsEncryptionSdkConfig(BuilderImpl builder) {
    this.commitmentPolicy = builder.commitmentPolicy();
    this.maxEncryptedDataKeys = builder.maxEncryptedDataKeys();
    this.netV4_0_0_RetryPolicy = builder.netV4_0_0_RetryPolicy();
  }

  public ESDKCommitmentPolicy commitmentPolicy() {
    return this.commitmentPolicy;
  }

  public long maxEncryptedDataKeys() {
    return this.maxEncryptedDataKeys;
  }

  /**
   * @return During Decryption, Allow or Forbid ESDK-NET v4.0.0 Behavior if the ESDK Message Header fails the Header Authentication check.
   */
  public NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy() {
    return this.netV4_0_0_RetryPolicy;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder commitmentPolicy(ESDKCommitmentPolicy commitmentPolicy);

    ESDKCommitmentPolicy commitmentPolicy();

    Builder maxEncryptedDataKeys(long maxEncryptedDataKeys);

    long maxEncryptedDataKeys();

    /**
     * @param netV4_0_0_RetryPolicy During Decryption, Allow or Forbid ESDK-NET v4.0.0 Behavior if the ESDK Message Header fails the Header Authentication check.
     */
    Builder netV4_0_0_RetryPolicy(NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy);

    /**
     * @return During Decryption, Allow or Forbid ESDK-NET v4.0.0 Behavior if the ESDK Message Header fails the Header Authentication check.
     */
    NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy();

    AwsEncryptionSdkConfig build();
  }

  static class BuilderImpl implements Builder {

    protected ESDKCommitmentPolicy commitmentPolicy;

    protected long maxEncryptedDataKeys;

    private boolean _maxEncryptedDataKeysSet = false;

    protected NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy;

    protected BuilderImpl() {}

    protected BuilderImpl(AwsEncryptionSdkConfig model) {
      this.commitmentPolicy = model.commitmentPolicy();
      this.maxEncryptedDataKeys = model.maxEncryptedDataKeys();
      this._maxEncryptedDataKeysSet = true;
      this.netV4_0_0_RetryPolicy = model.netV4_0_0_RetryPolicy();
    }

    public Builder commitmentPolicy(ESDKCommitmentPolicy commitmentPolicy) {
      this.commitmentPolicy = commitmentPolicy;
      return this;
    }

    public ESDKCommitmentPolicy commitmentPolicy() {
      return this.commitmentPolicy;
    }

    public Builder maxEncryptedDataKeys(long maxEncryptedDataKeys) {
      this.maxEncryptedDataKeys = maxEncryptedDataKeys;
      this._maxEncryptedDataKeysSet = true;
      return this;
    }

    public long maxEncryptedDataKeys() {
      return this.maxEncryptedDataKeys;
    }

    public Builder netV4_0_0_RetryPolicy(
      NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy
    ) {
      this.netV4_0_0_RetryPolicy = netV4_0_0_RetryPolicy;
      return this;
    }

    public NetV4_0_0_RetryPolicy netV4_0_0_RetryPolicy() {
      return this.netV4_0_0_RetryPolicy;
    }

    public AwsEncryptionSdkConfig build() {
      if (this._maxEncryptedDataKeysSet && this.maxEncryptedDataKeys() < 1) {
        throw new IllegalArgumentException(
          "`maxEncryptedDataKeys` must be greater than or equal to 1"
        );
      }
      return new AwsEncryptionSdkConfig(this);
    }
  }
}
