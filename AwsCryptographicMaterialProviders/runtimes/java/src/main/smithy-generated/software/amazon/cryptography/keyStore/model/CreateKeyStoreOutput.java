// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;

public class CreateKeyStoreOutput {
  private final String tableArn;

  protected CreateKeyStoreOutput(BuilderImpl builder) {
    this.tableArn = builder.tableArn();
  }

  public String tableArn() {
    return this.tableArn;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder tableArn(String tableArn);

    String tableArn();

    CreateKeyStoreOutput build();
  }

  static class BuilderImpl implements Builder {
    protected String tableArn;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateKeyStoreOutput model) {
      this.tableArn = model.tableArn();
    }

    public Builder tableArn(String tableArn) {
      this.tableArn = tableArn;
      return this;
    }

    public String tableArn() {
      return this.tableArn;
    }

    public CreateKeyStoreOutput build() {
      if (Objects.isNull(this.tableArn()))  {
        throw new IllegalArgumentException("Missing value for required field `tableArn`");
      }
      return new CreateKeyStoreOutput(this);
    }
  }
}
