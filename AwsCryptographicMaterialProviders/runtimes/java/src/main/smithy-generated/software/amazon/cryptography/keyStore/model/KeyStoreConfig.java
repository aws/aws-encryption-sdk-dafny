// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.kms.KmsClient;

public class KeyStoreConfig {
  private final String id;

  private final String ddbTableName;

  private final String kmsKeyArn;

  private final DynamoDbClient ddbClient;

  private final KmsClient kmsClient;

  protected KeyStoreConfig(BuilderImpl builder) {
    this.id = builder.id();
    this.ddbTableName = builder.ddbTableName();
    this.kmsKeyArn = builder.kmsKeyArn();
    this.ddbClient = builder.ddbClient();
    this.kmsClient = builder.kmsClient();
  }

  public String id() {
    return this.id;
  }

  public String ddbTableName() {
    return this.ddbTableName;
  }

  public String kmsKeyArn() {
    return this.kmsKeyArn;
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
    Builder id(String id);

    String id();

    Builder ddbTableName(String ddbTableName);

    String ddbTableName();

    Builder kmsKeyArn(String kmsKeyArn);

    String kmsKeyArn();

    Builder ddbClient(DynamoDbClient ddbClient);

    DynamoDbClient ddbClient();

    Builder kmsClient(KmsClient kmsClient);

    KmsClient kmsClient();

    KeyStoreConfig build();
  }

  static class BuilderImpl implements Builder {
    protected String id;

    protected String ddbTableName;

    protected String kmsKeyArn;

    protected DynamoDbClient ddbClient;

    protected KmsClient kmsClient;

    protected BuilderImpl() {
    }

    protected BuilderImpl(KeyStoreConfig model) {
      this.id = model.id();
      this.ddbTableName = model.ddbTableName();
      this.kmsKeyArn = model.kmsKeyArn();
      this.ddbClient = model.ddbClient();
      this.kmsClient = model.kmsClient();
    }

    public Builder id(String id) {
      this.id = id;
      return this;
    }

    public String id() {
      return this.id;
    }

    public Builder ddbTableName(String ddbTableName) {
      this.ddbTableName = ddbTableName;
      return this;
    }

    public String ddbTableName() {
      return this.ddbTableName;
    }

    public Builder kmsKeyArn(String kmsKeyArn) {
      this.kmsKeyArn = kmsKeyArn;
      return this;
    }

    public String kmsKeyArn() {
      return this.kmsKeyArn;
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
      if (Objects.isNull(this.kmsKeyArn()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsKeyArn`");
      }
      return new KeyStoreConfig(this);
    }
  }
}
