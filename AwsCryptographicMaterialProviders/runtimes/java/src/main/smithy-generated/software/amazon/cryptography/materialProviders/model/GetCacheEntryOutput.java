// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class GetCacheEntryOutput {
  private final Materials materials;

  private final int creationTime;

  private final int expiryTime;

  private final int messagesUsed;

  private final int bytesUsed;

  protected GetCacheEntryOutput(BuilderImpl builder) {
    this.materials = builder.materials();
    this.creationTime = builder.creationTime();
    this.expiryTime = builder.expiryTime();
    this.messagesUsed = builder.messagesUsed();
    this.bytesUsed = builder.bytesUsed();
  }

  public Materials materials() {
    return this.materials;
  }

  public int creationTime() {
    return this.creationTime;
  }

  public int expiryTime() {
    return this.expiryTime;
  }

  public int messagesUsed() {
    return this.messagesUsed;
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
    Builder materials(Materials materials);

    Materials materials();

    Builder creationTime(int creationTime);

    int creationTime();

    Builder expiryTime(int expiryTime);

    int expiryTime();

    Builder messagesUsed(int messagesUsed);

    int messagesUsed();

    Builder bytesUsed(int bytesUsed);

    int bytesUsed();

    GetCacheEntryOutput build();
  }

  static class BuilderImpl implements Builder {
    protected Materials materials;

    protected int creationTime;

    protected int expiryTime;

    protected int messagesUsed;

    protected int bytesUsed;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetCacheEntryOutput model) {
      this.materials = model.materials();
      this.creationTime = model.creationTime();
      this.expiryTime = model.expiryTime();
      this.messagesUsed = model.messagesUsed();
      this.bytesUsed = model.bytesUsed();
    }

    public Builder materials(Materials materials) {
      this.materials = materials;
      return this;
    }

    public Materials materials() {
      return this.materials;
    }

    public Builder creationTime(int creationTime) {
      this.creationTime = creationTime;
      return this;
    }

    public int creationTime() {
      return this.creationTime;
    }

    public Builder expiryTime(int expiryTime) {
      this.expiryTime = expiryTime;
      return this;
    }

    public int expiryTime() {
      return this.expiryTime;
    }

    public Builder messagesUsed(int messagesUsed) {
      this.messagesUsed = messagesUsed;
      return this;
    }

    public int messagesUsed() {
      return this.messagesUsed;
    }

    public Builder bytesUsed(int bytesUsed) {
      this.bytesUsed = bytesUsed;
      return this;
    }

    public int bytesUsed() {
      return this.bytesUsed;
    }

    public GetCacheEntryOutput build() {
      if (Objects.isNull(this.materials()))  {
        throw new IllegalArgumentException("Missing value for required field `materials`");
      }
      if (Objects.isNull(this.creationTime()))  {
        throw new IllegalArgumentException("Missing value for required field `creationTime`");
      }
      if (Objects.nonNull(this.creationTime()) && this.creationTime() < 0) {
        throw new IllegalArgumentException("`creationTime` must be greater than or equal to 0");
      }
      if (Objects.isNull(this.expiryTime()))  {
        throw new IllegalArgumentException("Missing value for required field `expiryTime`");
      }
      if (Objects.nonNull(this.expiryTime()) && this.expiryTime() < 0) {
        throw new IllegalArgumentException("`expiryTime` must be greater than or equal to 0");
      }
      if (Objects.isNull(this.messagesUsed()))  {
        throw new IllegalArgumentException("Missing value for required field `messagesUsed`");
      }
      if (Objects.nonNull(this.messagesUsed()) && this.messagesUsed() < 0) {
        throw new IllegalArgumentException("`messagesUsed` must be greater than or equal to 0");
      }
      if (Objects.isNull(this.bytesUsed()))  {
        throw new IllegalArgumentException("Missing value for required field `bytesUsed`");
      }
      if (Objects.nonNull(this.bytesUsed()) && this.bytesUsed() < 0) {
        throw new IllegalArgumentException("`bytesUsed` must be greater than or equal to 0");
      }
      return new GetCacheEntryOutput(this);
    }
  }
}
