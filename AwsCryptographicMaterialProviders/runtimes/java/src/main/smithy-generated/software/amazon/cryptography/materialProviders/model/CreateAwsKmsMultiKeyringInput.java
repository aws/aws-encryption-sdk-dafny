// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import software.amazon.cryptography.materialproviders.ClientSupplier;
import software.amazon.cryptography.materialproviders.IClientSupplier;

public class CreateAwsKmsMultiKeyringInput {
  private final String generator;

  private final List<String> kmsKeyIds;

  private final IClientSupplier clientSupplier;

  private final List<String> grantTokens;

  protected CreateAwsKmsMultiKeyringInput(BuilderImpl builder) {
    this.generator = builder.generator();
    this.kmsKeyIds = builder.kmsKeyIds();
    this.clientSupplier = builder.clientSupplier();
    this.grantTokens = builder.grantTokens();
  }

  public String generator() {
    return this.generator;
  }

  public List<String> kmsKeyIds() {
    return this.kmsKeyIds;
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
    Builder generator(String generator);

    String generator();

    Builder kmsKeyIds(List<String> kmsKeyIds);

    List<String> kmsKeyIds();

    Builder clientSupplier(IClientSupplier clientSupplier);

    IClientSupplier clientSupplier();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String generator;

    protected List<String> kmsKeyIds;

    protected IClientSupplier clientSupplier;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsMultiKeyringInput model) {
      this.generator = model.generator();
      this.kmsKeyIds = model.kmsKeyIds();
      this.clientSupplier = model.clientSupplier();
      this.grantTokens = model.grantTokens();
    }

    public Builder generator(String generator) {
      this.generator = generator;
      return this;
    }

    public String generator() {
      return this.generator;
    }

    public Builder kmsKeyIds(List<String> kmsKeyIds) {
      this.kmsKeyIds = kmsKeyIds;
      return this;
    }

    public List<String> kmsKeyIds() {
      return this.kmsKeyIds;
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

    public CreateAwsKmsMultiKeyringInput build() {
      return new CreateAwsKmsMultiKeyringInput(this);
    }
  }
}
