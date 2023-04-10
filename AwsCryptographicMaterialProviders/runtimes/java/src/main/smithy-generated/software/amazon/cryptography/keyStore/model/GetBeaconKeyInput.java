// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;

public class GetBeaconKeyInput {
  private final String branchKeyIdentifier;

  private final String awsKmsKeyArn;

  protected GetBeaconKeyInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.awsKmsKeyArn = builder.awsKmsKeyArn();
  }

  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  public String awsKmsKeyArn() {
    return this.awsKmsKeyArn;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    String branchKeyIdentifier();

    Builder awsKmsKeyArn(String awsKmsKeyArn);

    String awsKmsKeyArn();

    GetBeaconKeyInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyIdentifier;

    protected String awsKmsKeyArn;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBeaconKeyInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.awsKmsKeyArn = model.awsKmsKeyArn();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public Builder awsKmsKeyArn(String awsKmsKeyArn) {
      this.awsKmsKeyArn = awsKmsKeyArn;
      return this;
    }

    public String awsKmsKeyArn() {
      return this.awsKmsKeyArn;
    }

    public GetBeaconKeyInput build() {
      if (Objects.isNull(this.branchKeyIdentifier()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyIdentifier`");
      }
      return new GetBeaconKeyInput(this);
    }
  }
}
