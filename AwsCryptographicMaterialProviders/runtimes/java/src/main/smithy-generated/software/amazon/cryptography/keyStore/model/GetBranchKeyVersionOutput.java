// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetBranchKeyVersionOutput {
  private final String branchKeyVersion;

  private final ByteBuffer branchKey;

  protected GetBranchKeyVersionOutput(BuilderImpl builder) {
    this.branchKeyVersion = builder.branchKeyVersion();
    this.branchKey = builder.branchKey();
  }

  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  public ByteBuffer branchKey() {
    return this.branchKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder branchKeyVersion(String branchKeyVersion);

    String branchKeyVersion();

    Builder branchKey(ByteBuffer branchKey);

    ByteBuffer branchKey();

    GetBranchKeyVersionOutput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyVersion;

    protected ByteBuffer branchKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBranchKeyVersionOutput model) {
      this.branchKeyVersion = model.branchKeyVersion();
      this.branchKey = model.branchKey();
    }

    public Builder branchKeyVersion(String branchKeyVersion) {
      this.branchKeyVersion = branchKeyVersion;
      return this;
    }

    public String branchKeyVersion() {
      return this.branchKeyVersion;
    }

    public Builder branchKey(ByteBuffer branchKey) {
      this.branchKey = branchKey;
      return this;
    }

    public ByteBuffer branchKey() {
      return this.branchKey;
    }

    public GetBranchKeyVersionOutput build() {
      if (Objects.isNull(this.branchKeyVersion()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyVersion`");
      }
      if (Objects.isNull(this.branchKey()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKey`");
      }
      return new GetBranchKeyVersionOutput(this);
    }
  }
}
