// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class DigestInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer message;

  protected DigestInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.message = builder.message();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer message() {
    return this.message;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder digestAlgorithm(DigestAlgorithm digestAlgorithm);

    DigestAlgorithm digestAlgorithm();

    Builder message(ByteBuffer message);

    ByteBuffer message();

    DigestInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer message;

    protected BuilderImpl() {
    }

    protected BuilderImpl(DigestInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.message = model.message();
    }

    public Builder digestAlgorithm(DigestAlgorithm digestAlgorithm) {
      this.digestAlgorithm = digestAlgorithm;
      return this;
    }

    public DigestAlgorithm digestAlgorithm() {
      return this.digestAlgorithm;
    }

    public Builder message(ByteBuffer message) {
      this.message = message;
      return this;
    }

    public ByteBuffer message() {
      return this.message;
    }

    public DigestInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.message()))  {
        throw new IllegalArgumentException("Missing value for required field `message`");
      }
      return new DigestInput(this);
    }
  }
}
