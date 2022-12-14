// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class CommitmentPolicy {
  private final ESDKCommitmentPolicy ESDK;

  protected CommitmentPolicy(BuilderImpl builder) {
    this.ESDK = builder.ESDK();
  }

  public ESDKCommitmentPolicy ESDK() {
    return this.ESDK;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ESDK(ESDKCommitmentPolicy ESDK);

    ESDKCommitmentPolicy ESDK();

    CommitmentPolicy build();
  }

  static class BuilderImpl implements Builder {
    protected ESDKCommitmentPolicy ESDK;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CommitmentPolicy model) {
      this.ESDK = model.ESDK();
    }

    public Builder ESDK(ESDKCommitmentPolicy ESDK) {
      this.ESDK = ESDK;
      return this;
    }

    public ESDKCommitmentPolicy ESDK() {
      return this.ESDK;
    }

    public CommitmentPolicy build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`CommitmentPolicy` is a Union. A Union MUST have one and only one value set.");
      }
      return new CommitmentPolicy(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.ESDK};
      boolean haveOneNonNull = false;
      for (Object o : allValues) {
        if (Objects.nonNull(o)) {
          if (haveOneNonNull) {
            return false;
          }
          haveOneNonNull = true;
        }
      }
      return haveOneNonNull;
    }
  }
}
