// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.Keyring;

public class CreateMultiKeyringInput {
  private final Keyring generator;

  private final List<Keyring> childKeyrings;

  protected CreateMultiKeyringInput(BuilderImpl builder) {
    this.generator = builder.generator();
    this.childKeyrings = builder.childKeyrings();
  }

  public Keyring generator() {
    return this.generator;
  }

  public List<Keyring> childKeyrings() {
    return this.childKeyrings;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder generator(Keyring generator);

    Keyring generator();

    Builder childKeyrings(List<Keyring> childKeyrings);

    List<Keyring> childKeyrings();

    CreateMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected Keyring generator;

    protected List<Keyring> childKeyrings;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateMultiKeyringInput model) {
      this.generator = model.generator();
      this.childKeyrings = model.childKeyrings();
    }

    public Builder generator(Keyring generator) {
      this.generator = generator;
      return this;
    }

    public Keyring generator() {
      return this.generator;
    }

    public Builder childKeyrings(List<Keyring> childKeyrings) {
      this.childKeyrings = childKeyrings;
      return this;
    }

    public List<Keyring> childKeyrings() {
      return this.childKeyrings;
    }

    public CreateMultiKeyringInput build() {
      if (Objects.isNull(this.childKeyrings()))  {
        throw new IllegalArgumentException("Missing value for required field `childKeyrings`");
      }
      return new CreateMultiKeyringInput(this);
    }
  }
}
