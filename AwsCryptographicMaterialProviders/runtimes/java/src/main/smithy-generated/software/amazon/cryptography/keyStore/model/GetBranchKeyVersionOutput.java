// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetBranchKeyVersionOutput {
  private final ByteBuffer branchKey;

  private final String branchKeyVersion;

  protected GetBranchKeyVersionOutput(BuilderImpl builder) {
    this.branchKey = builder.branchKey();
    this.branchKeyVersion = builder.branchKeyVersion();
  }

  public ByteBuffer branchKey() {
    return this.branchKey;
  }

  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder branchKey(ByteBuffer branchKey);

    ByteBuffer branchKey();

    Builder branchKeyVersion(String branchKeyVersion);

    String branchKeyVersion();

    GetBranchKeyVersionOutput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer branchKey;

    protected String branchKeyVersion;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBranchKeyVersionOutput model) {
      this.branchKey = model.branchKey();
      this.branchKeyVersion = model.branchKeyVersion();
    }

    public Builder branchKey(ByteBuffer branchKey) {
      this.branchKey = branchKey;
      return this;
    }

    public ByteBuffer branchKey() {
      return this.branchKey;
    }

    public Builder branchKeyVersion(String branchKeyVersion) {
      this.branchKeyVersion = branchKeyVersion;
      return this;
    }

    public String branchKeyVersion() {
      return this.branchKeyVersion;
    }

    public GetBranchKeyVersionOutput build() {
      if (Objects.isNull(this.branchKey()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKey`");
      }
      if (Objects.isNull(this.branchKeyVersion()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyVersion`");
      }
      return new GetBranchKeyVersionOutput(this);
    }
  }
}
