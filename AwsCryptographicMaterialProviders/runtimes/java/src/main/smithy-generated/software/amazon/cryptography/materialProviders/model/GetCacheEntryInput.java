// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetCacheEntryInput {
  private final ByteBuffer identifier;

  private final Long bytesUsed;

  protected GetCacheEntryInput(BuilderImpl builder) {
    this.identifier = builder.identifier();
    this.bytesUsed = builder.bytesUsed();
  }

  public ByteBuffer identifier() {
    return this.identifier;
  }

  public Long bytesUsed() {
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

    Builder bytesUsed(Long bytesUsed);

    Long bytesUsed();

    GetCacheEntryInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer identifier;

    protected Long bytesUsed;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetCacheEntryInput model) {
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

    public Builder bytesUsed(Long bytesUsed) {
      this.bytesUsed = bytesUsed;
      return this;
    }

    public Long bytesUsed() {
      return this.bytesUsed;
    }

    public GetCacheEntryInput build() {
      if (Objects.isNull(this.identifier()))  {
        throw new IllegalArgumentException("Missing value for required field `identifier`");
      }
      return new GetCacheEntryInput(this);
    }
  }
}
