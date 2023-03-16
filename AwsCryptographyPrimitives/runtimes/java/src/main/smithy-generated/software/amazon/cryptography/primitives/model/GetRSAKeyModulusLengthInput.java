// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetRSAKeyModulusLengthInput {
  private final ByteBuffer publicKey;

  protected GetRSAKeyModulusLengthInput(BuilderImpl builder) {
    this.publicKey = builder.publicKey();
  }

  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder publicKey(ByteBuffer publicKey);

    ByteBuffer publicKey();

    GetRSAKeyModulusLengthInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer publicKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetRSAKeyModulusLengthInput model) {
      this.publicKey = model.publicKey();
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public GetRSAKeyModulusLengthInput build() {
      if (Objects.isNull(this.publicKey()))  {
        throw new IllegalArgumentException("Missing value for required field `publicKey`");
      }
      return new GetRSAKeyModulusLengthInput(this);
    }
  }
}
