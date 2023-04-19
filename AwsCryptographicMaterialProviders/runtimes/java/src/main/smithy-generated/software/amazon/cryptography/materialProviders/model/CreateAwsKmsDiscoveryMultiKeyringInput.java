// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialProviders.ClientSupplier;
import software.amazon.cryptography.materialProviders.IClientSupplier;

public class CreateAwsKmsDiscoveryMultiKeyringInput {
  private final List<String> regions;

  private final DiscoveryFilter discoveryFilter;

  private final IClientSupplier clientSupplier;

  private final List<String> grantTokens;

  protected CreateAwsKmsDiscoveryMultiKeyringInput(BuilderImpl builder) {
    this.regions = builder.regions();
    this.discoveryFilter = builder.discoveryFilter();
    this.clientSupplier = builder.clientSupplier();
    this.grantTokens = builder.grantTokens();
  }

  public List<String> regions() {
    return this.regions;
  }

  public DiscoveryFilter discoveryFilter() {
    return this.discoveryFilter;
  }

  public IClientSupplier clientSupplier() {
    return this.clientSupplier;
  }

  public List<String> grantTokens() {
    return this.grantTokens;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder regions(List<String> regions);

    List<String> regions();

    Builder discoveryFilter(DiscoveryFilter discoveryFilter);

    DiscoveryFilter discoveryFilter();

    Builder clientSupplier(IClientSupplier clientSupplier);

    IClientSupplier clientSupplier();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsDiscoveryMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected List<String> regions;

    protected DiscoveryFilter discoveryFilter;

    protected IClientSupplier clientSupplier;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsDiscoveryMultiKeyringInput model) {
      this.regions = model.regions();
      this.discoveryFilter = model.discoveryFilter();
      this.clientSupplier = model.clientSupplier();
      this.grantTokens = model.grantTokens();
    }

    public Builder regions(List<String> regions) {
      this.regions = regions;
      return this;
    }

    public List<String> regions() {
      return this.regions;
    }

    public Builder discoveryFilter(DiscoveryFilter discoveryFilter) {
      this.discoveryFilter = discoveryFilter;
      return this;
    }

    public DiscoveryFilter discoveryFilter() {
      return this.discoveryFilter;
    }

    public Builder clientSupplier(IClientSupplier clientSupplier) {
      this.clientSupplier = ClientSupplier.wrap(clientSupplier);
      return this;
    }

    public IClientSupplier clientSupplier() {
      return this.clientSupplier;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsDiscoveryMultiKeyringInput build() {
      if (Objects.isNull(this.regions()))  {
        throw new IllegalArgumentException("Missing value for required field `regions`");
      }
      return new CreateAwsKmsDiscoveryMultiKeyringInput(this);
    }
  }
}
