// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import com.amazonaws.services.kms.AWSKMS;
import java.util.List;
import java.util.Objects;

public class CreateAwsKmsMrkKeyringInput {
  private final String kmsKeyId;

  private final AWSKMS kmsClient;

  private final List<String> grantTokens;

  protected CreateAwsKmsMrkKeyringInput(BuilderImpl builder) {
    this.kmsKeyId = builder.kmsKeyId();
    this.kmsClient = builder.kmsClient();
    this.grantTokens = builder.grantTokens();
  }

  public String kmsKeyId() {
    return this.kmsKeyId;
  }

  public AWSKMS kmsClient() {
    return this.kmsClient;
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
    Builder kmsKeyId(String kmsKeyId);

    String kmsKeyId();

    Builder kmsClient(AWSKMS kmsClient);

    AWSKMS kmsClient();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsMrkKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String kmsKeyId;

    protected AWSKMS kmsClient;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsMrkKeyringInput model) {
      this.kmsKeyId = model.kmsKeyId();
      this.kmsClient = model.kmsClient();
      this.grantTokens = model.grantTokens();
    }

    public Builder kmsKeyId(String kmsKeyId) {
      this.kmsKeyId = kmsKeyId;
      return this;
    }

    public String kmsKeyId() {
      return this.kmsKeyId;
    }

    public Builder kmsClient(AWSKMS kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public AWSKMS kmsClient() {
      return this.kmsClient;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsMrkKeyringInput build() {
      if (Objects.isNull(this.kmsKeyId()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsKeyId`");
      }
      if (Objects.isNull(this.kmsClient()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsClient`");
      }
      return new CreateAwsKmsMrkKeyringInput(this);
    }
  }
}