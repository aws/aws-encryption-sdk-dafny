// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.kms.KmsClient;

public class KeyStoreConfig {
  private final String ddbTableName;

  private final KMSConfiguration kmsConfiguration;

  private final String logicalKeyStoreName;

  private final String id;

  private final List<String> grantTokens;

  private final DynamoDbClient ddbClient;

  private final KmsClient kmsClient;

  protected KeyStoreConfig(BuilderImpl builder) {
    this.ddbTableName = builder.ddbTableName();
    this.kmsConfiguration = builder.kmsConfiguration();
    this.logicalKeyStoreName = builder.logicalKeyStoreName();
    this.id = builder.id();
    this.grantTokens = builder.grantTokens();
    this.ddbClient = builder.ddbClient();
    this.kmsClient = builder.kmsClient();
  }

  public String ddbTableName() {
    return this.ddbTableName;
  }

  public KMSConfiguration kmsConfiguration() {
    return this.kmsConfiguration;
  }

  public String logicalKeyStoreName() {
    return this.logicalKeyStoreName;
  }

  public String id() {
    return this.id;
  }

  public List<String> grantTokens() {
    return this.grantTokens;
  }

  public DynamoDbClient ddbClient() {
    return this.ddbClient;
  }

  public KmsClient kmsClient() {
    return this.kmsClient;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder ddbTableName(String ddbTableName);

    String ddbTableName();

    Builder kmsConfiguration(KMSConfiguration kmsConfiguration);

    KMSConfiguration kmsConfiguration();

    Builder logicalKeyStoreName(String logicalKeyStoreName);

    String logicalKeyStoreName();

    Builder id(String id);

    String id();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    Builder ddbClient(DynamoDbClient ddbClient);

    DynamoDbClient ddbClient();

    Builder kmsClient(KmsClient kmsClient);

    KmsClient kmsClient();

    KeyStoreConfig build();
  }

  static class BuilderImpl implements Builder {
    protected String ddbTableName;

    protected KMSConfiguration kmsConfiguration;

    protected String logicalKeyStoreName;

    protected String id;

    protected List<String> grantTokens;

    protected DynamoDbClient ddbClient;

    protected KmsClient kmsClient;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KeyStoreConfig model) {
      this.ddbTableName = model.ddbTableName();
      this.kmsConfiguration = model.kmsConfiguration();
      this.logicalKeyStoreName = model.logicalKeyStoreName();
      this.id = model.id();
      this.grantTokens = model.grantTokens();
      this.ddbClient = model.ddbClient();
      this.kmsClient = model.kmsClient();
    }

    public Builder ddbTableName(String ddbTableName) {
      this.ddbTableName = ddbTableName;
      return this;
    }

    public String ddbTableName() {
      return this.ddbTableName;
    }

    public Builder kmsConfiguration(KMSConfiguration kmsConfiguration) {
      this.kmsConfiguration = kmsConfiguration;
      return this;
    }

    public KMSConfiguration kmsConfiguration() {
      return this.kmsConfiguration;
    }

    public Builder logicalKeyStoreName(String logicalKeyStoreName) {
      this.logicalKeyStoreName = logicalKeyStoreName;
      return this;
    }

    public String logicalKeyStoreName() {
      return this.logicalKeyStoreName;
    }

    public Builder id(String id) {
      this.id = id;
      return this;
    }

    public String id() {
      return this.id;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public Builder ddbClient(DynamoDbClient ddbClient) {
      this.ddbClient = ddbClient;
      return this;
    }

    public DynamoDbClient ddbClient() {
      return this.ddbClient;
    }

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public KeyStoreConfig build() {
      if (Objects.isNull(this.ddbTableName()))  {
        throw new IllegalArgumentException("Missing value for required field `ddbTableName`");
      }
      if (Objects.nonNull(this.ddbTableName()) && this.ddbTableName().length() < 3) {
        throw new IllegalArgumentException("The size of `ddbTableName` must be greater than or equal to 3");
      }
      if (Objects.nonNull(this.ddbTableName()) && this.ddbTableName().length() > 255) {
        throw new IllegalArgumentException("The size of `ddbTableName` must be less than or equal to 255");
      }
      if (Objects.isNull(this.kmsConfiguration()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsConfiguration`");
      }
      if (Objects.isNull(this.logicalKeyStoreName()))  {
        throw new IllegalArgumentException("Missing value for required field `logicalKeyStoreName`");
      }
      return new KeyStoreConfig(this);
    }
  }
}
