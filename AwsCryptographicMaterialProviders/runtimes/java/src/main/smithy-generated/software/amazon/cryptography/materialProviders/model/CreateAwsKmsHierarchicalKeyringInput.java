// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.kms.KmsClient;

public class CreateAwsKmsHierarchicalKeyringInput {
  private final String branchKeyId;

  private final String kmsKeyId;

  private final KmsClient kmsClient;

  private final DynamoDbClient ddbClient;

  private final String branchKeyStoreArn;

  private final Long ttlSeconds;

  private final int maxCacheSize;

  private final List<String> grantTokens;

  protected CreateAwsKmsHierarchicalKeyringInput(BuilderImpl builder) {
    this.branchKeyId = builder.branchKeyId();
    this.kmsKeyId = builder.kmsKeyId();
    this.kmsClient = builder.kmsClient();
    this.ddbClient = builder.ddbClient();
    this.branchKeyStoreArn = builder.branchKeyStoreArn();
    this.ttlSeconds = builder.ttlSeconds();
    this.maxCacheSize = builder.maxCacheSize();
    this.grantTokens = builder.grantTokens();
  }

  public String branchKeyId() {
    return this.branchKeyId;
  }

  public String kmsKeyId() {
    return this.kmsKeyId;
  }

  public KmsClient kmsClient() {
    return this.kmsClient;
  }

  public DynamoDbClient ddbClient() {
    return this.ddbClient;
  }

  public String branchKeyStoreArn() {
    return this.branchKeyStoreArn;
  }

  public Long ttlSeconds() {
    return this.ttlSeconds;
  }

  public int maxCacheSize() {
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

    Builder kmsClient(KmsClient kmsClient);

    KmsClient kmsClient();

    Builder ddbClient(DynamoDbClient ddbClient);

    DynamoDbClient ddbClient();

    Builder branchKeyStoreArn(String branchKeyStoreArn);

    String branchKeyStoreArn();

    Builder ttlSeconds(Long ttlSeconds);

    Long ttlSeconds();

    Builder maxCacheSize(int maxCacheSize);

    int maxCacheSize();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsHierarchicalKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyId;

    protected String kmsKeyId;

    protected KmsClient kmsClient;

    protected DynamoDbClient ddbClient;

    protected String branchKeyStoreArn;

    protected Long ttlSeconds;

    protected int maxCacheSize;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsHierarchicalKeyringInput model) {
      this.branchKeyId = model.branchKeyId();
      this.kmsKeyId = model.kmsKeyId();
      this.kmsClient = model.kmsClient();
      this.ddbClient = model.ddbClient();
      this.branchKeyStoreArn = model.branchKeyStoreArn();
      this.ttlSeconds = model.ttlSeconds();
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

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public Builder ddbClient(DynamoDbClient ddbClient) {
      this.ddbClient = ddbClient;
      return this;
    }

    public DynamoDbClient ddbClient() {
      return this.ddbClient;
    }

    public Builder branchKeyStoreArn(String branchKeyStoreArn) {
      this.branchKeyStoreArn = branchKeyStoreArn;
      return this;
    }

    public String branchKeyStoreArn() {
      return this.branchKeyStoreArn;
    }

    public Builder ttlSeconds(Long ttlSeconds) {
      this.ttlSeconds = ttlSeconds;
      return this;
    }

    public Long ttlSeconds() {
      return this.ttlSeconds;
    }

    public Builder maxCacheSize(int maxCacheSize) {
      this.maxCacheSize = maxCacheSize;
      return this;
    }

    public int maxCacheSize() {
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
      if (Objects.isNull(this.branchKeyStoreArn()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyStoreArn`");
      }
      if (Objects.isNull(this.ttlSeconds()))  {
        throw new IllegalArgumentException("Missing value for required field `ttlSeconds`");
      }
      if (Objects.nonNull(this.ttlSeconds()) && this.ttlSeconds() < 1) {
        throw new IllegalArgumentException("`ttlSeconds` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.maxCacheSize()) && this.maxCacheSize() < 0) {
        throw new IllegalArgumentException("`maxCacheSize` must be greater than or equal to 0");
      }
      return new CreateAwsKmsHierarchicalKeyringInput(this);
    }
  }
}
