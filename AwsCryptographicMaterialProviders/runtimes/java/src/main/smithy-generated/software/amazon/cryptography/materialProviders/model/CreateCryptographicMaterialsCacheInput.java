// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class CreateCryptographicMaterialsCacheInput {
  private final int entryCapacity;

  private final int entryPruningTailSize;

  protected CreateCryptographicMaterialsCacheInput(BuilderImpl builder) {
    this.entryCapacity = builder.entryCapacity();
    this.entryPruningTailSize = builder.entryPruningTailSize();
  }

  public int entryCapacity() {
    return this.entryCapacity;
  }

  public int entryPruningTailSize() {
    return this.entryPruningTailSize;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder entryCapacity(int entryCapacity);

    int entryCapacity();

    Builder entryPruningTailSize(int entryPruningTailSize);

    int entryPruningTailSize();

    CreateCryptographicMaterialsCacheInput build();
  }

  static class BuilderImpl implements Builder {
    protected int entryCapacity;

    protected int entryPruningTailSize;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateCryptographicMaterialsCacheInput model) {
      this.entryCapacity = model.entryCapacity();
      this.entryPruningTailSize = model.entryPruningTailSize();
    }

    public Builder entryCapacity(int entryCapacity) {
      this.entryCapacity = entryCapacity;
      return this;
    }

    public int entryCapacity() {
      return this.entryCapacity;
    }

    public Builder entryPruningTailSize(int entryPruningTailSize) {
      this.entryPruningTailSize = entryPruningTailSize;
      return this;
    }

    public int entryPruningTailSize() {
      return this.entryPruningTailSize;
    }

    public CreateCryptographicMaterialsCacheInput build() {
      if (Objects.isNull(this.entryCapacity()))  {
        throw new IllegalArgumentException("Missing value for required field `entryCapacity`");
      }
      if (Objects.nonNull(this.entryCapacity()) && this.entryCapacity() < 0) {
        throw new IllegalArgumentException("`entryCapacity` must be greater than or equal to 0");
      }
      if (Objects.nonNull(this.entryPruningTailSize()) && this.entryPruningTailSize() < 0) {
        throw new IllegalArgumentException("`entryPruningTailSize` must be greater than or equal to 0");
      }
      return new CreateCryptographicMaterialsCacheInput(this);
    }
  }
}
