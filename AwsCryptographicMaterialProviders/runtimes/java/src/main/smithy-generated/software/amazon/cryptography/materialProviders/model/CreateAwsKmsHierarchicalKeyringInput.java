// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;
import software.amazon.cryptography.keyStore.KeyStore;
import software.amazon.cryptography.materialProviders.BranchKeyIdSupplier;
import software.amazon.cryptography.materialProviders.IBranchKeyIdSupplier;

public class CreateAwsKmsHierarchicalKeyringInput {
  private final String branchKeyId;

  private final IBranchKeyIdSupplier branchKeyIdSupplier;

  private final KeyStore keyStore;

  private final long ttlSeconds;

  private final int maxCacheSize;

  protected CreateAwsKmsHierarchicalKeyringInput(BuilderImpl builder) {
    this.branchKeyId = builder.branchKeyId();
    this.branchKeyIdSupplier = builder.branchKeyIdSupplier();
    this.keyStore = builder.keyStore();
    this.ttlSeconds = builder.ttlSeconds();
    this.maxCacheSize = builder.maxCacheSize();
  }

  public String branchKeyId() {
    return this.branchKeyId;
  }

  public IBranchKeyIdSupplier branchKeyIdSupplier() {
    return this.branchKeyIdSupplier;
  }

  public KeyStore keyStore() {
    return this.keyStore;
  }

  public long ttlSeconds() {
    return this.ttlSeconds;
  }

  public int maxCacheSize() {
    return this.maxCacheSize;
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

    Builder branchKeyIdSupplier(IBranchKeyIdSupplier branchKeyIdSupplier);

    IBranchKeyIdSupplier branchKeyIdSupplier();

    Builder keyStore(KeyStore keyStore);

    KeyStore keyStore();

    Builder ttlSeconds(long ttlSeconds);

    long ttlSeconds();

    Builder maxCacheSize(int maxCacheSize);

    int maxCacheSize();

    CreateAwsKmsHierarchicalKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyId;

    protected IBranchKeyIdSupplier branchKeyIdSupplier;

    protected KeyStore keyStore;

    protected long ttlSeconds;

    protected int maxCacheSize;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsHierarchicalKeyringInput model) {
      this.branchKeyId = model.branchKeyId();
      this.branchKeyIdSupplier = model.branchKeyIdSupplier();
      this.keyStore = model.keyStore();
      this.ttlSeconds = model.ttlSeconds();
      this.maxCacheSize = model.maxCacheSize();
    }

    public Builder branchKeyId(String branchKeyId) {
      this.branchKeyId = branchKeyId;
      return this;
    }

    public String branchKeyId() {
      return this.branchKeyId;
    }

    public Builder branchKeyIdSupplier(IBranchKeyIdSupplier branchKeyIdSupplier) {
      this.branchKeyIdSupplier = BranchKeyIdSupplier.wrap(branchKeyIdSupplier);
      return this;
    }

    public IBranchKeyIdSupplier branchKeyIdSupplier() {
      return this.branchKeyIdSupplier;
    }

    public Builder keyStore(KeyStore keyStore) {
      this.keyStore = keyStore;
      return this;
    }

    public KeyStore keyStore() {
      return this.keyStore;
    }

    public Builder ttlSeconds(long ttlSeconds) {
      this.ttlSeconds = ttlSeconds;
      return this;
    }

    public long ttlSeconds() {
      return this.ttlSeconds;
    }

    public Builder maxCacheSize(int maxCacheSize) {
      this.maxCacheSize = maxCacheSize;
      return this;
    }

    public int maxCacheSize() {
      return this.maxCacheSize;
    }

    public CreateAwsKmsHierarchicalKeyringInput build() {
      if (Objects.isNull(this.keyStore()))  {
        throw new IllegalArgumentException("Missing value for required field `keyStore`");
      }
      if (Objects.isNull(this.ttlSeconds()))  {
        throw new IllegalArgumentException("Missing value for required field `ttlSeconds`");
      }
      if (Objects.nonNull(this.ttlSeconds()) && this.ttlSeconds() < 0) {
        throw new IllegalArgumentException("`ttlSeconds` must be greater than or equal to 0");
      }
      if (Objects.nonNull(this.maxCacheSize()) && this.maxCacheSize() < 0) {
        throw new IllegalArgumentException("`maxCacheSize` must be greater than or equal to 0");
      }
      return new CreateAwsKmsHierarchicalKeyringInput(this);
    }
  }
}
