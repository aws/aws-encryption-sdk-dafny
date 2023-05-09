// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class ValidEncryptionMaterialsTransitionInput {
  private final EncryptionMaterials start;

  private final EncryptionMaterials stop;

  protected ValidEncryptionMaterialsTransitionInput(BuilderImpl builder) {
    this.start = builder.start();
    this.stop = builder.stop();
  }

  public EncryptionMaterials start() {
    return this.start;
  }

  public EncryptionMaterials stop() {
    return this.stop;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder start(EncryptionMaterials start);

    EncryptionMaterials start();

    Builder stop(EncryptionMaterials stop);

    EncryptionMaterials stop();

    ValidEncryptionMaterialsTransitionInput build();
  }

  static class BuilderImpl implements Builder {
    protected EncryptionMaterials start;

    protected EncryptionMaterials stop;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ValidEncryptionMaterialsTransitionInput model) {
      this.start = model.start();
      this.stop = model.stop();
    }

    public Builder start(EncryptionMaterials start) {
      this.start = start;
      return this;
    }

    public EncryptionMaterials start() {
      return this.start;
    }

    public Builder stop(EncryptionMaterials stop) {
      this.stop = stop;
      return this;
    }

    public EncryptionMaterials stop() {
      return this.stop;
    }

    public ValidEncryptionMaterialsTransitionInput build() {
      if (Objects.isNull(this.start()))  {
        throw new IllegalArgumentException("Missing value for required field `start`");
      }
      if (Objects.isNull(this.stop()))  {
        throw new IllegalArgumentException("Missing value for required field `stop`");
      }
      return new ValidEncryptionMaterialsTransitionInput(this);
    }
  }
}
