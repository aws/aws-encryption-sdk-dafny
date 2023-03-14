// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class UpdaterUsageMetadataInput {
  private final ByteBuffer identifier;

  private final int bytesUsed;

  protected UpdaterUsageMetadataInput(BuilderImpl builder) {
    this.identifier = builder.identifier();
    this.bytesUsed = builder.bytesUsed();
  }

  public ByteBuffer identifier() {
    return this.identifier;
  }

  public int bytesUsed() {
    return this.bytesUsed;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder identifier(ByteBuffer identifier);

    ByteBuffer identifier();

    Builder bytesUsed(int bytesUsed);

    int bytesUsed();

    UpdaterUsageMetadataInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer identifier;

    protected int bytesUsed;

    protected BuilderImpl() {
    }

    protected BuilderImpl(UpdaterUsageMetadataInput model) {
      this.identifier = model.identifier();
      this.bytesUsed = model.bytesUsed();
    }

    public Builder identifier(ByteBuffer identifier) {
      this.identifier = identifier;
      return this;
    }

    public ByteBuffer identifier() {
      return this.identifier;
    }

    public Builder bytesUsed(int bytesUsed) {
      this.bytesUsed = bytesUsed;
      return this;
    }

    public int bytesUsed() {
      return this.bytesUsed;
    }

    public UpdaterUsageMetadataInput build() {
      if (Objects.isNull(this.identifier()))  {
        throw new IllegalArgumentException("Missing value for required field `identifier`");
      }
      if (Objects.isNull(this.bytesUsed()))  {
        throw new IllegalArgumentException("Missing value for required field `bytesUsed`");
      }
      if (Objects.nonNull(this.bytesUsed()) && this.bytesUsed() < 0) {
        throw new IllegalArgumentException("`bytesUsed` must be greater than or equal to 0");
      }
      return new UpdaterUsageMetadataInput(this);
    }
  }
}
