// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class EdkWrappingAlgorithm {
  private final DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING;

  private final IntermediateKeyWrapping IntermediateKeyWrapping;

  protected EdkWrappingAlgorithm(BuilderImpl builder) {
    this.DIRECT_KEY_WRAPPING = builder.DIRECT_KEY_WRAPPING();
    this.IntermediateKeyWrapping = builder.IntermediateKeyWrapping();
  }

  public DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING() {
    return this.DIRECT_KEY_WRAPPING;
  }

  public IntermediateKeyWrapping IntermediateKeyWrapping() {
    return this.IntermediateKeyWrapping;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING);

    DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING();

    Builder IntermediateKeyWrapping(IntermediateKeyWrapping IntermediateKeyWrapping);

    IntermediateKeyWrapping IntermediateKeyWrapping();

    EdkWrappingAlgorithm build();
  }

  static class BuilderImpl implements Builder {
    protected DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING;

    protected IntermediateKeyWrapping IntermediateKeyWrapping;

    protected BuilderImpl() {
    }

    protected BuilderImpl(EdkWrappingAlgorithm model) {
      this.DIRECT_KEY_WRAPPING = model.DIRECT_KEY_WRAPPING();
      this.IntermediateKeyWrapping = model.IntermediateKeyWrapping();
    }

    public Builder DIRECT_KEY_WRAPPING(DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING) {
      this.DIRECT_KEY_WRAPPING = DIRECT_KEY_WRAPPING;
      return this;
    }

    public DIRECT_KEY_WRAPPING DIRECT_KEY_WRAPPING() {
      return this.DIRECT_KEY_WRAPPING;
    }

    public Builder IntermediateKeyWrapping(IntermediateKeyWrapping IntermediateKeyWrapping) {
      this.IntermediateKeyWrapping = IntermediateKeyWrapping;
      return this;
    }

    public IntermediateKeyWrapping IntermediateKeyWrapping() {
      return this.IntermediateKeyWrapping;
    }

    public EdkWrappingAlgorithm build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`EdkWrappingAlgorithm` is a Union. A Union MUST have one and only one value set.");
      }
      return new EdkWrappingAlgorithm(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.DIRECT_KEY_WRAPPING, this.IntermediateKeyWrapping};
      boolean haveOneNonNull = false;
      for (Object o : allValues) {
        if (Objects.nonNull(o)) {
          if (haveOneNonNull) {
            return false;
          }
          haveOneNonNull = true;
        }
      }
      return haveOneNonNull;
    }
  }
}
