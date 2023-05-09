// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;
import software.amazon.cryptography.primitives.model.AES_GCM;

public class Encrypt {
  private final AES_GCM AES_GCM;

  protected Encrypt(BuilderImpl builder) {
    this.AES_GCM = builder.AES_GCM();
  }

  public AES_GCM AES_GCM() {
    return this.AES_GCM;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder AES_GCM(AES_GCM AES_GCM);

    AES_GCM AES_GCM();

    Encrypt build();
  }

  static class BuilderImpl implements Builder {
    protected AES_GCM AES_GCM;

    protected BuilderImpl() {
    }

    protected BuilderImpl(Encrypt model) {
      this.AES_GCM = model.AES_GCM();
    }

    public Builder AES_GCM(AES_GCM AES_GCM) {
      this.AES_GCM = AES_GCM;
      return this;
    }

    public AES_GCM AES_GCM() {
      return this.AES_GCM;
    }

    public Encrypt build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`Encrypt` is a Union. A Union MUST have one and only one value set.");
      }
      return new Encrypt(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.AES_GCM};
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
