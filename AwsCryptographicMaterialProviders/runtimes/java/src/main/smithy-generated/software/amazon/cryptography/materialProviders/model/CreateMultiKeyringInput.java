// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.IKeyring;
import software.amazon.cryptography.materialProviders.Keyring;

public class CreateMultiKeyringInput {
  private final Keyring generator;

  private final List<IKeyring> childKeyrings;

  protected CreateMultiKeyringInput(BuilderImpl builder) {
    this.generator = builder.generator();
    this.childKeyrings = builder.childKeyrings();
  }

  public Keyring generator() {
    return this.generator;
  }

  public List<IKeyring> childKeyrings() {
    return this.childKeyrings;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder generator(IKeyring generator);

    Keyring generator();

    Builder childKeyrings(List<IKeyring> childKeyrings);

    List<IKeyring> childKeyrings();

    CreateMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected Keyring generator;

    protected List<IKeyring> childKeyrings;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateMultiKeyringInput model) {
      this.generator = model.generator();
      this.childKeyrings = model.childKeyrings();
    }

    public Builder generator(IKeyring generator) {
      this.generator = Keyring.wrap(generator);
      return this;
    }

    public Keyring generator() {
      return this.generator;
    }

    public Builder childKeyrings(List<IKeyring> childKeyrings) {
      this.childKeyrings = childKeyrings;
      return this;
    }

    public List<IKeyring> childKeyrings() {
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
