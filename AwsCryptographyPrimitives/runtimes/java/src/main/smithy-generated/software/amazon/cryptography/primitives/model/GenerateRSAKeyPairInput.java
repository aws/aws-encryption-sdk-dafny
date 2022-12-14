// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

public class GenerateRSAKeyPairInput {
  private final int strength;

  protected GenerateRSAKeyPairInput(BuilderImpl builder) {
    this.strength = builder.strength();
  }

  public int strength() {
    return this.strength;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder strength(int strength);

    int strength();

    GenerateRSAKeyPairInput build();
  }

  static class BuilderImpl implements Builder {
    protected int strength;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateRSAKeyPairInput model) {
      this.strength = model.strength();
    }

    public Builder strength(int strength) {
      this.strength = strength;
      return this;
    }

    public int strength() {
      return this.strength;
    }

    public GenerateRSAKeyPairInput build() {
      if (Objects.isNull(this.strength()))  {
        throw new IllegalArgumentException("Missing value for required field `strength`");
      }
      if (Objects.nonNull(this.strength()) && this.strength() < 81) {
        throw new IllegalArgumentException("`strength` must be greater than or equal to 81");
      }
      if (Objects.nonNull(this.strength()) && this.strength() > 4096) {
        throw new IllegalArgumentException("`strength` must be less than or equal to 4096.");
      }
      return new GenerateRSAKeyPairInput(this);
    }
  }
}
