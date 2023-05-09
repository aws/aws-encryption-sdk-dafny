// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class GetCacheEntryOutput {
  private final Materials materials;

  private final long creationTime;

  private final long expiryTime;

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

  public long creationTime() {
    return this.creationTime;
  }

  public long expiryTime() {
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

    Builder creationTime(long creationTime);

    long creationTime();

    Builder expiryTime(long expiryTime);

    long expiryTime();

    Builder messagesUsed(int messagesUsed);

    int messagesUsed();

    Builder bytesUsed(int bytesUsed);

    int bytesUsed();

    GetCacheEntryOutput build();
  }

  static class BuilderImpl implements Builder {
    protected Materials materials;

    protected long creationTime;

    private boolean _creationTimeSet = false;

    protected long expiryTime;

    private boolean _expiryTimeSet = false;

    protected int messagesUsed;

    private boolean _messagesUsedSet = false;

    protected int bytesUsed;

    private boolean _bytesUsedSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetCacheEntryOutput model) {
      this.materials = model.materials();
      this.creationTime = model.creationTime();
      this._creationTimeSet = true;
      this.expiryTime = model.expiryTime();
      this._expiryTimeSet = true;
      this.messagesUsed = model.messagesUsed();
      this._messagesUsedSet = true;
      this.bytesUsed = model.bytesUsed();
      this._bytesUsedSet = true;
    }

    public Builder materials(Materials materials) {
      this.materials = materials;
      return this;
    }

    public Materials materials() {
      return this.materials;
    }

    public Builder creationTime(long creationTime) {
      this.creationTime = creationTime;
      this._creationTimeSet = true;
      return this;
    }

    public long creationTime() {
      return this.creationTime;
    }

    public Builder expiryTime(long expiryTime) {
      this.expiryTime = expiryTime;
      this._expiryTimeSet = true;
      return this;
    }

    public long expiryTime() {
      return this.expiryTime;
    }

    public Builder messagesUsed(int messagesUsed) {
      this.messagesUsed = messagesUsed;
      this._messagesUsedSet = true;
      return this;
    }

    public int messagesUsed() {
      return this.messagesUsed;
    }

    public Builder bytesUsed(int bytesUsed) {
      this.bytesUsed = bytesUsed;
      this._bytesUsedSet = true;
      return this;
    }

    public int bytesUsed() {
      return this.bytesUsed;
    }

    public GetCacheEntryOutput build() {
      if (Objects.isNull(this.materials()))  {
        throw new IllegalArgumentException("Missing value for required field `materials`");
      }
      if (!this._creationTimeSet) {
        throw new IllegalArgumentException("Missing value for required field `creationTime`");
      }
      if (this._creationTimeSet && this.creationTime() < 0) {
        throw new IllegalArgumentException("`creationTime` must be greater than or equal to 0");
      }
      if (!this._expiryTimeSet) {
        throw new IllegalArgumentException("Missing value for required field `expiryTime`");
      }
      if (this._expiryTimeSet && this.expiryTime() < 0) {
        throw new IllegalArgumentException("`expiryTime` must be greater than or equal to 0");
      }
      if (!this._messagesUsedSet) {
        throw new IllegalArgumentException("Missing value for required field `messagesUsed`");
      }
      if (this._messagesUsedSet && this.messagesUsed() < 0) {
        throw new IllegalArgumentException("`messagesUsed` must be greater than or equal to 0");
      }
      if (!this._bytesUsedSet) {
        throw new IllegalArgumentException("Missing value for required field `bytesUsed`");
      }
      if (this._bytesUsedSet && this.bytesUsed() < 0) {
        throw new IllegalArgumentException("`bytesUsed` must be greater than or equal to 0");
      }
      return new GetCacheEntryOutput(this);
    }
  }
}
