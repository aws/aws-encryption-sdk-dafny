// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import software.amazon.cryptography.materialProviders.IKeyring;
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
    <I extends IKeyring> Builder generator(I generator);

    Keyring generator();

    <I extends IKeyring> Builder childKeyrings(List<I> childKeyrings);

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

    public <I extends IKeyring> Builder generator(I generator) {
      this.generator = Keyring.create(generator);
      return this;
    }

    public Keyring generator() {
      return this.generator;
    }

    public <I extends IKeyring> Builder childKeyrings(List<I> childKeyrings) {
      this.childKeyrings = childKeyrings.stream().sequential()
              .map(Keyring::create)
              .collect(Collectors.toList());
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
