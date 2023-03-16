// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

public class GenerateRSAKeyPairInput {
  private final int lengthBits;

  protected GenerateRSAKeyPairInput(BuilderImpl builder) {
    this.lengthBits = builder.lengthBits();
  }

  public int lengthBits() {
    return this.lengthBits;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder lengthBits(int lengthBits);

    int lengthBits();

    GenerateRSAKeyPairInput build();
  }

  static class BuilderImpl implements Builder {
    protected int lengthBits;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateRSAKeyPairInput model) {
      this.lengthBits = model.lengthBits();
    }

    public Builder lengthBits(int lengthBits) {
      this.lengthBits = lengthBits;
      return this;
    }

    public int lengthBits() {
      return this.lengthBits;
    }

    public GenerateRSAKeyPairInput build() {
      if (Objects.isNull(this.lengthBits()))  {
        throw new IllegalArgumentException("Missing value for required field `lengthBits`");
      }
      if (Objects.nonNull(this.lengthBits()) && this.lengthBits() < 81) {
        throw new IllegalArgumentException("`lengthBits` must be greater than or equal to 81");
      }
      if (Objects.nonNull(this.lengthBits()) && this.lengthBits() > 4096) {
        throw new IllegalArgumentException("`lengthBits` must be less than or equal to 4096.");
      }
      return new GenerateRSAKeyPairInput(this);
    }
  }
}
