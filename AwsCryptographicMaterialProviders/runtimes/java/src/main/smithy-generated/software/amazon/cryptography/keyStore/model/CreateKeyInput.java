// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;

public class CreateKeyInput {
  private final String awsKmsKeyArn;

  protected CreateKeyInput(BuilderImpl builder) {
    this.awsKmsKeyArn = builder.awsKmsKeyArn();
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
    Builder awsKmsKeyArn(String awsKmsKeyArn);

    String awsKmsKeyArn();

    CreateKeyInput build();
  }

  static class BuilderImpl implements Builder {
    protected String awsKmsKeyArn;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateKeyInput model) {
      this.awsKmsKeyArn = model.awsKmsKeyArn();
    }

    public Builder awsKmsKeyArn(String awsKmsKeyArn) {
      this.awsKmsKeyArn = awsKmsKeyArn;
      return this;
    }

    public String awsKmsKeyArn() {
      return this.awsKmsKeyArn;
    }

    public CreateKeyInput build() {
      if (Objects.isNull(this.awsKmsKeyArn()))  {
        throw new IllegalArgumentException("Missing value for required field `awsKmsKeyArn`");
      }
      return new CreateKeyInput(this);
    }
  }
}
