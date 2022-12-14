// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GenerateRandomBytesOutput {
  private final ByteBuffer data;

  protected GenerateRandomBytesOutput(BuilderImpl builder) {
    this.data = builder.data();
  }

  public ByteBuffer data() {
    return this.data;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder data(ByteBuffer data);

    ByteBuffer data();

    GenerateRandomBytesOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer data;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GenerateRandomBytesOutput model) {
      this.data = model.data();
    }

    public Builder data(ByteBuffer data) {
      this.data = data;
      return this;
    }

    public ByteBuffer data() {
      return this.data;
    }

    public GenerateRandomBytesOutput build() {
      if (Objects.isNull(this.data()))  {
        throw new IllegalArgumentException("Missing value for required field `data`");
      }
      return new GenerateRandomBytesOutput(this);
    }
  }
}
