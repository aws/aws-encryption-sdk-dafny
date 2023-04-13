// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.List;
import java.util.Objects;

public class GetBranchKeyVersionInput {
  private final String branchKeyIdentifier;

  private final String branchKeyVersion;

  private final String awsKmsKeyArn;

  private final List<String> grantTokens;

  protected GetBranchKeyVersionInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.branchKeyVersion = builder.branchKeyVersion();
    this.awsKmsKeyArn = builder.awsKmsKeyArn();
    this.grantTokens = builder.grantTokens();
  }

  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  public String awsKmsKeyArn() {
    return this.awsKmsKeyArn;
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
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    String branchKeyIdentifier();

    Builder branchKeyVersion(String branchKeyVersion);

    String branchKeyVersion();

    Builder awsKmsKeyArn(String awsKmsKeyArn);

    String awsKmsKeyArn();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    GetBranchKeyVersionInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyIdentifier;

    protected String branchKeyVersion;

    protected String awsKmsKeyArn;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBranchKeyVersionInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.branchKeyVersion = model.branchKeyVersion();
      this.awsKmsKeyArn = model.awsKmsKeyArn();
      this.grantTokens = model.grantTokens();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public Builder branchKeyVersion(String branchKeyVersion) {
      this.branchKeyVersion = branchKeyVersion;
      return this;
    }

    public String branchKeyVersion() {
      return this.branchKeyVersion;
    }

    public Builder awsKmsKeyArn(String awsKmsKeyArn) {
      this.awsKmsKeyArn = awsKmsKeyArn;
      return this;
    }

    public String awsKmsKeyArn() {
      return this.awsKmsKeyArn;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public GetBranchKeyVersionInput build() {
      if (Objects.isNull(this.branchKeyIdentifier()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyIdentifier`");
      }
      if (Objects.isNull(this.branchKeyVersion()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyVersion`");
      }
      return new GetBranchKeyVersionInput(this);
    }
  }
}
