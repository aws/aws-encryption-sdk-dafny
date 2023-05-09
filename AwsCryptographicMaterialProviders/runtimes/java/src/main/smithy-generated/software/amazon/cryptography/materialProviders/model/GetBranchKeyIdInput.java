// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Map;
import java.util.Objects;

public class GetBranchKeyIdInput {
  private final Map<String, String> encryptionContext;

  protected GetBranchKeyIdInput(BuilderImpl builder) {
    this.encryptionContext = builder.encryptionContext();
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    GetBranchKeyIdInput build();
  }

  static class BuilderImpl implements Builder {
    protected Map<String, String> encryptionContext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBranchKeyIdInput model) {
      this.encryptionContext = model.encryptionContext();
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public GetBranchKeyIdInput build() {
      if (Objects.isNull(this.encryptionContext()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionContext`");
      }
      return new GetBranchKeyIdInput(this);
    }
  }
}
