// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import java.util.List;
import java.util.Objects;

public class CreateAwsKmsDiscoveryKeyringInput {
  private final IKeyManagementServiceClient kmsClient;

  private final DiscoveryFilter discoveryFilter;

  private final List<String> grantTokens;

  protected CreateAwsKmsDiscoveryKeyringInput(BuilderImpl builder) {
    this.kmsClient = builder.kmsClient();
    this.discoveryFilter = builder.discoveryFilter();
    this.grantTokens = builder.grantTokens();
  }

  public IKeyManagementServiceClient kmsClient() {
    return this.kmsClient;
  }

  public DiscoveryFilter discoveryFilter() {
    return this.discoveryFilter;
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
    Builder kmsClient(IKeyManagementServiceClient kmsClient);

    IKeyManagementServiceClient kmsClient();

    Builder discoveryFilter(DiscoveryFilter discoveryFilter);

    DiscoveryFilter discoveryFilter();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsDiscoveryKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected IKeyManagementServiceClient kmsClient;

    protected DiscoveryFilter discoveryFilter;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsDiscoveryKeyringInput model) {
      this.kmsClient = model.kmsClient();
      this.discoveryFilter = model.discoveryFilter();
      this.grantTokens = model.grantTokens();
    }

    public Builder kmsClient(IKeyManagementServiceClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public IKeyManagementServiceClient kmsClient() {
      return this.kmsClient;
    }

    public Builder discoveryFilter(DiscoveryFilter discoveryFilter) {
      this.discoveryFilter = discoveryFilter;
      return this;
    }

    public DiscoveryFilter discoveryFilter() {
      return this.discoveryFilter;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsDiscoveryKeyringInput build() {
      if (Objects.isNull(this.kmsClient()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsClient`");
      }
      return new CreateAwsKmsDiscoveryKeyringInput(this);
    }
  }
}
