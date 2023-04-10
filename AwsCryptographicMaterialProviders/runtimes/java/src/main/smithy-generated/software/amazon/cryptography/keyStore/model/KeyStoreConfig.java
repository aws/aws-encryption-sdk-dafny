// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.kms.KmsClient;

public class KeyStoreConfig {
  private final String ddbTableName;

  private final DynamoDbClient ddbClient;

  private final KmsClient kmsClient;

  protected KeyStoreConfig(BuilderImpl builder) {
    this.ddbTableName = builder.ddbTableName();
    this.ddbClient = builder.ddbClient();
    this.kmsClient = builder.kmsClient();
  }

  public String ddbTableName() {
    return this.ddbTableName;
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

    Builder ddbClient(DynamoDbClient ddbClient);

    DynamoDbClient ddbClient();

    Builder kmsClient(KmsClient kmsClient);

    KmsClient kmsClient();

    KeyStoreConfig build();
  }

  static class BuilderImpl implements Builder {
    protected String ddbTableName;

    protected DynamoDbClient ddbClient;

    protected KmsClient kmsClient;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KeyStoreConfig model) {
      this.ddbTableName = model.ddbTableName();
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
      if (Objects.nonNull(this.ddbTableName()) && this.ddbTableName().length() < 3) {
        throw new IllegalArgumentException("The size of `ddbTableName` must be greater than or equal to 3");
      }
      if (Objects.nonNull(this.ddbTableName()) && this.ddbTableName().length() > 255) {
        throw new IllegalArgumentException("The size of `ddbTableName` must be less than or equal to 255");
      }
      return new KeyStoreConfig(this);
    }
  }
}
