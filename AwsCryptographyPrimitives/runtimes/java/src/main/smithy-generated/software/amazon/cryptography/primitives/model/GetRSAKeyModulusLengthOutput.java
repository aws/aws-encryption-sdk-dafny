// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.util.Objects;

public class GetRSAKeyModulusLengthOutput {
  private final int length;

  protected GetRSAKeyModulusLengthOutput(BuilderImpl builder) {
    this.length = builder.length();
  }

  public int length() {
    return this.length;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder length(int length);

    int length();

    GetRSAKeyModulusLengthOutput build();
  }

  static class BuilderImpl implements Builder {
    protected int length;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetRSAKeyModulusLengthOutput model) {
      this.length = model.length();
    }

    public Builder length(int length) {
      this.length = length;
      return this;
    }

    public int length() {
      return this.length;
    }

    public GetRSAKeyModulusLengthOutput build() {
      if (Objects.isNull(this.length()))  {
        throw new IllegalArgumentException("Missing value for required field `length`");
      }
      if (Objects.nonNull(this.length()) && this.length() < 81) {
        throw new IllegalArgumentException("`length` must be greater than or equal to 81");
      }
      return new GetRSAKeyModulusLengthOutput(this);
    }
  }
}
