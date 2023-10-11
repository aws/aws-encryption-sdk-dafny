// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public class CreateDefaultClientSupplierInput {
  protected CreateDefaultClientSupplierInput(BuilderImpl builder) {
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    CreateDefaultClientSupplierInput build();
  }

  static class BuilderImpl implements Builder {
    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateDefaultClientSupplierInput model) {
    }

    public CreateDefaultClientSupplierInput build() {
      return new CreateDefaultClientSupplierInput(this);
    }
  }
}
