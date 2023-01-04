// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import Dafny.Com.Amazonaws.Dynamodb.Types.IDynamoDB__20120810Client;
import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
import java.util.List;
import java.util.Objects;

public class CreateAwsKmsHierarchicalKeyringInput {
  private final String branchKeyId;

  private final String kmsKeyId;

  private final IKeyManagementServiceClient kmsClient;

  private final IDynamoDB__20120810Client ddbClient;

  private final String branchKeysTableName;

  private final Long ttlMilliseconds;

  private final Integer maxCacheSize;

  private final List<String> grantTokens;

  protected CreateAwsKmsHierarchicalKeyringInput(BuilderImpl builder) {
    this.branchKeyId = builder.branchKeyId();
    this.kmsKeyId = builder.kmsKeyId();
    this.kmsClient = builder.kmsClient();
    this.ddbClient = builder.ddbClient();
    this.branchKeysTableName = builder.branchKeysTableName();
    this.ttlMilliseconds = builder.ttlMilliseconds();
    this.maxCacheSize = builder.maxCacheSize();
    this.grantTokens = builder.grantTokens();
  }

  public String branchKeyId() {
    return this.branchKeyId;
  }

  public String kmsKeyId() {
    return this.kmsKeyId;
  }

  public IKeyManagementServiceClient kmsClient() {
    return this.kmsClient;
  }

  public IDynamoDB__20120810Client ddbClient() {
    return this.ddbClient;
  }

  public String branchKeysTableName() {
    return this.branchKeysTableName;
  }

  public Long ttlMilliseconds() {
    return this.ttlMilliseconds;
  }

  public Integer maxCacheSize() {
    return this.maxCacheSize;
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
    Builder branchKeyId(String branchKeyId);

    String branchKeyId();

    Builder kmsKeyId(String kmsKeyId);

    String kmsKeyId();

    Builder kmsClient(IKeyManagementServiceClient kmsClient);

    IKeyManagementServiceClient kmsClient();

    Builder ddbClient(IDynamoDB__20120810Client ddbClient);

    IDynamoDB__20120810Client ddbClient();

    Builder branchKeysTableName(String branchKeysTableName);

    String branchKeysTableName();

    Builder ttlMilliseconds(Long ttlMilliseconds);

    Long ttlMilliseconds();

    Builder maxCacheSize(Integer maxCacheSize);

    Integer maxCacheSize();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsHierarchicalKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyId;

    protected String kmsKeyId;

    protected IKeyManagementServiceClient kmsClient;

    protected IDynamoDB__20120810Client ddbClient;

    protected String branchKeysTableName;

    protected Long ttlMilliseconds;

    protected Integer maxCacheSize;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsHierarchicalKeyringInput model) {
      this.branchKeyId = model.branchKeyId();
      this.kmsKeyId = model.kmsKeyId();
      this.kmsClient = model.kmsClient();
      this.ddbClient = model.ddbClient();
      this.branchKeysTableName = model.branchKeysTableName();
      this.ttlMilliseconds = model.ttlMilliseconds();
      this.maxCacheSize = model.maxCacheSize();
      this.grantTokens = model.grantTokens();
    }

    public Builder branchKeyId(String branchKeyId) {
      this.branchKeyId = branchKeyId;
      return this;
    }

    public String branchKeyId() {
      return this.branchKeyId;
    }

    public Builder kmsKeyId(String kmsKeyId) {
      this.kmsKeyId = kmsKeyId;
      return this;
    }

    public String kmsKeyId() {
      return this.kmsKeyId;
    }

    public Builder kmsClient(IKeyManagementServiceClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public IKeyManagementServiceClient kmsClient() {
      return this.kmsClient;
    }

    public Builder ddbClient(IDynamoDB__20120810Client ddbClient) {
      this.ddbClient = ddbClient;
      return this;
    }

    public IDynamoDB__20120810Client ddbClient() {
      return this.ddbClient;
    }

    public Builder branchKeysTableName(String branchKeysTableName) {
      this.branchKeysTableName = branchKeysTableName;
      return this;
    }

    public String branchKeysTableName() {
      return this.branchKeysTableName;
    }

    public Builder ttlMilliseconds(Long ttlMilliseconds) {
      this.ttlMilliseconds = ttlMilliseconds;
      return this;
    }

    public Long ttlMilliseconds() {
      return this.ttlMilliseconds;
    }

    public Builder maxCacheSize(Integer maxCacheSize) {
      this.maxCacheSize = maxCacheSize;
      return this;
    }

    public Integer maxCacheSize() {
      return this.maxCacheSize;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsHierarchicalKeyringInput build() {
      if (Objects.isNull(this.branchKeyId()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyId`");
      }
      if (Objects.isNull(this.kmsKeyId()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsKeyId`");
      }
      if (Objects.isNull(this.kmsClient()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsClient`");
      }
      if (Objects.isNull(this.ddbClient()))  {
        throw new IllegalArgumentException("Missing value for required field `ddbClient`");
      }
      if (Objects.isNull(this.branchKeysTableName()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeysTableName`");
      }
      if (Objects.isNull(this.ttlMilliseconds()))  {
        throw new IllegalArgumentException("Missing value for required field `ttlMilliseconds`");
      }
      if (Objects.nonNull(this.ttlMilliseconds()) && this.ttlMilliseconds() < 1) {
        throw new IllegalArgumentException("`ttlMilliseconds` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.maxCacheSize()) && this.maxCacheSize() < 1) {
        throw new IllegalArgumentException("`maxCacheSize` must be greater than or equal to 1");
      }
      return new CreateAwsKmsHierarchicalKeyringInput(this);
    }
  }
}
