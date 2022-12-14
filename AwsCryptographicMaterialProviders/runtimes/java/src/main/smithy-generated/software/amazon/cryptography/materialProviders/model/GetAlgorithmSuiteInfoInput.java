// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetAlgorithmSuiteInfoInput {
  private final ByteBuffer binaryId;

  protected GetAlgorithmSuiteInfoInput(BuilderImpl builder) {
    this.binaryId = builder.binaryId();
  }

  public ByteBuffer binaryId() {
    return this.binaryId;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder binaryId(ByteBuffer binaryId);

    ByteBuffer binaryId();

    GetAlgorithmSuiteInfoInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer binaryId;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetAlgorithmSuiteInfoInput model) {
      this.binaryId = model.binaryId();
    }

    public Builder binaryId(ByteBuffer binaryId) {
      this.binaryId = binaryId;
      return this;
    }

    public ByteBuffer binaryId() {
      return this.binaryId;
    }

    public GetAlgorithmSuiteInfoInput build() {
      if (Objects.isNull(this.binaryId()))  {
        throw new IllegalArgumentException("Missing value for required field `binaryId`");
      }
      return new GetAlgorithmSuiteInfoInput(this);
    }
  }
}
