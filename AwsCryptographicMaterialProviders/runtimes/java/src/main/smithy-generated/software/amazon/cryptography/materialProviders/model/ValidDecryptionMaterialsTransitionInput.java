// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class ValidDecryptionMaterialsTransitionInput {
  private final DecryptionMaterials start;

  private final DecryptionMaterials stop;

  protected ValidDecryptionMaterialsTransitionInput(BuilderImpl builder) {
    this.start = builder.start();
    this.stop = builder.stop();
  }

  public DecryptionMaterials start() {
    return this.start;
  }

  public DecryptionMaterials stop() {
    return this.stop;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder start(DecryptionMaterials start);

    DecryptionMaterials start();

    Builder stop(DecryptionMaterials stop);

    DecryptionMaterials stop();

    ValidDecryptionMaterialsTransitionInput build();
  }

  static class BuilderImpl implements Builder {
    protected DecryptionMaterials start;

    protected DecryptionMaterials stop;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ValidDecryptionMaterialsTransitionInput model) {
      this.start = model.start();
      this.stop = model.stop();
    }

    public Builder start(DecryptionMaterials start) {
      this.start = start;
      return this;
    }

    public DecryptionMaterials start() {
      return this.start;
    }

    public Builder stop(DecryptionMaterials stop) {
      this.stop = stop;
      return this;
    }

    public DecryptionMaterials stop() {
      return this.stop;
    }

    public ValidDecryptionMaterialsTransitionInput build() {
      if (Objects.isNull(this.start()))  {
        throw new IllegalArgumentException("Missing value for required field `start`");
      }
      if (Objects.isNull(this.stop()))  {
        throw new IllegalArgumentException("Missing value for required field `stop`");
      }
      return new ValidDecryptionMaterialsTransitionInput(this);
    }
  }
}
