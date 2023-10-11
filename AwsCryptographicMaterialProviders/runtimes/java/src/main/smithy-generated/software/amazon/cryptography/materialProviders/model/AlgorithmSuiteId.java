// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class AlgorithmSuiteId {
  private final ESDKAlgorithmSuiteId ESDK;

  private final DBEAlgorithmSuiteId DBE;

  protected AlgorithmSuiteId(BuilderImpl builder) {
    this.ESDK = builder.ESDK();
    this.DBE = builder.DBE();
  }

  public ESDKAlgorithmSuiteId ESDK() {
    return this.ESDK;
  }

  public DBEAlgorithmSuiteId DBE() {
    return this.DBE;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ESDK(ESDKAlgorithmSuiteId ESDK);

    ESDKAlgorithmSuiteId ESDK();

    Builder DBE(DBEAlgorithmSuiteId DBE);

    DBEAlgorithmSuiteId DBE();

    AlgorithmSuiteId build();
  }

  static class BuilderImpl implements Builder {
    protected ESDKAlgorithmSuiteId ESDK;

    protected DBEAlgorithmSuiteId DBE;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AlgorithmSuiteId model) {
      this.ESDK = model.ESDK();
      this.DBE = model.DBE();
    }

    public Builder ESDK(ESDKAlgorithmSuiteId ESDK) {
      this.ESDK = ESDK;
      return this;
    }

    public ESDKAlgorithmSuiteId ESDK() {
      return this.ESDK;
    }

    public Builder DBE(DBEAlgorithmSuiteId DBE) {
      this.DBE = DBE;
      return this;
    }

    public DBEAlgorithmSuiteId DBE() {
      return this.DBE;
    }

    public AlgorithmSuiteId build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`AlgorithmSuiteId` is a Union. A Union MUST have one and only one value set.");
      }
      return new AlgorithmSuiteId(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.ESDK, this.DBE};
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
