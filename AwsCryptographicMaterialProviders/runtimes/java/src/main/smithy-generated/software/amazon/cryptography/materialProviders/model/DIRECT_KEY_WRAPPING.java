// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

public class DIRECT_KEY_WRAPPING {
  protected DIRECT_KEY_WRAPPING(BuilderImpl builder) {
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    DIRECT_KEY_WRAPPING build();
  }

  static class BuilderImpl implements Builder {
    protected BuilderImpl() {
    }

    protected BuilderImpl(DIRECT_KEY_WRAPPING model) {
    }

    public DIRECT_KEY_WRAPPING build() {
      return new DIRECT_KEY_WRAPPING(this);
    }
  }
}
