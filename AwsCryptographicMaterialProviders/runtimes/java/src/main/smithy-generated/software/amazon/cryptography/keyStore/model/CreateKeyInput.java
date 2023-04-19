// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.List;

public class CreateKeyInput {
  private final List<String> grantTokens;

  protected CreateKeyInput(BuilderImpl builder) {
    this.grantTokens = builder.grantTokens();
  }

  public List<String> grantTokens() {
    return this.grantTokens;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateKeyInput build();
  }

  static class BuilderImpl implements Builder {
    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateKeyInput model) {
      this.grantTokens = model.grantTokens();
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateKeyInput build() {
      return new CreateKeyInput(this);
    }
  }
}
