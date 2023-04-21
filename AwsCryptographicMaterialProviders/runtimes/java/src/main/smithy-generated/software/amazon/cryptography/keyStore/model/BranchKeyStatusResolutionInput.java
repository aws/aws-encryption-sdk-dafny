// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.List;
import java.util.Objects;

public class BranchKeyStatusResolutionInput {
  private final String branchKeyIdentifier;

  private final List<String> grantTokens;

  protected BranchKeyStatusResolutionInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.grantTokens = builder.grantTokens();
  }

  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
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
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    String branchKeyIdentifier();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    BranchKeyStatusResolutionInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyIdentifier;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(BranchKeyStatusResolutionInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.grantTokens = model.grantTokens();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public BranchKeyStatusResolutionInput build() {
      if (Objects.isNull(this.branchKeyIdentifier()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyIdentifier`");
      }
      return new BranchKeyStatusResolutionInput(this);
    }
  }
}
