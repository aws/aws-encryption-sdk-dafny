// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.HierarchicalMaterials;

public class GetActiveBranchKeyOutput {
  private final HierarchicalMaterials hierarchicalMaterials;

  protected GetActiveBranchKeyOutput(BuilderImpl builder) {
    this.hierarchicalMaterials = builder.hierarchicalMaterials();
  }

  public HierarchicalMaterials hierarchicalMaterials() {
    return this.hierarchicalMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder hierarchicalMaterials(HierarchicalMaterials hierarchicalMaterials);

    HierarchicalMaterials hierarchicalMaterials();

    GetActiveBranchKeyOutput build();
  }

  static class BuilderImpl implements Builder {
    protected HierarchicalMaterials hierarchicalMaterials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetActiveBranchKeyOutput model) {
      this.hierarchicalMaterials = model.hierarchicalMaterials();
    }

    public Builder hierarchicalMaterials(HierarchicalMaterials hierarchicalMaterials) {
      this.hierarchicalMaterials = hierarchicalMaterials;
      return this;
    }

    public HierarchicalMaterials hierarchicalMaterials() {
      return this.hierarchicalMaterials;
    }

    public GetActiveBranchKeyOutput build() {
      if (Objects.isNull(this.hierarchicalMaterials()))  {
        throw new IllegalArgumentException("Missing value for required field `hierarchicalMaterials`");
      }
      return new GetActiveBranchKeyOutput(this);
    }
  }
}
