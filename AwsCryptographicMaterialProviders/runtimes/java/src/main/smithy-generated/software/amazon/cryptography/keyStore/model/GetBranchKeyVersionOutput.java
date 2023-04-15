// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.BranchKeyMaterials;

public class GetBranchKeyVersionOutput {
  private final BranchKeyMaterials branchKeyMaterials;

  protected GetBranchKeyVersionOutput(BuilderImpl builder) {
    this.branchKeyMaterials = builder.branchKeyMaterials();
  }

  public BranchKeyMaterials branchKeyMaterials() {
    return this.branchKeyMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder branchKeyMaterials(BranchKeyMaterials branchKeyMaterials);

    BranchKeyMaterials branchKeyMaterials();

    GetBranchKeyVersionOutput build();
  }

  static class BuilderImpl implements Builder {
    protected BranchKeyMaterials branchKeyMaterials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBranchKeyVersionOutput model) {
      this.branchKeyMaterials = model.branchKeyMaterials();
    }

    public Builder branchKeyMaterials(BranchKeyMaterials branchKeyMaterials) {
      this.branchKeyMaterials = branchKeyMaterials;
      return this;
    }

    public BranchKeyMaterials branchKeyMaterials() {
      return this.branchKeyMaterials;
    }

    public GetBranchKeyVersionOutput build() {
      if (Objects.isNull(this.branchKeyMaterials()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyMaterials`");
      }
      return new GetBranchKeyVersionOutput(this);
    }
  }
}
