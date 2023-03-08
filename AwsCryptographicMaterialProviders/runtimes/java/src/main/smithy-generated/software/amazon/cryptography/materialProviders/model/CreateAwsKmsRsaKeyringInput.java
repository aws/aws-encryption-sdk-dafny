// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.model.EncryptionAlgorithmSpec;

public class CreateAwsKmsRsaKeyringInput {
  private final ByteBuffer publicKey;

  private final String kmsKeyId;

  private final EncryptionAlgorithmSpec encryptionAlgorithm;

  private final KmsClient kmsClient;

  private final List<String> grantTokens;

  protected CreateAwsKmsRsaKeyringInput(BuilderImpl builder) {
    this.publicKey = builder.publicKey();
    this.kmsKeyId = builder.kmsKeyId();
    this.encryptionAlgorithm = builder.encryptionAlgorithm();
    this.kmsClient = builder.kmsClient();
    this.grantTokens = builder.grantTokens();
  }

  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  public String kmsKeyId() {
    return this.kmsKeyId;
  }

  public EncryptionAlgorithmSpec encryptionAlgorithm() {
    return this.encryptionAlgorithm;
  }

  public KmsClient kmsClient() {
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
    Builder publicKey(ByteBuffer publicKey);

    ByteBuffer publicKey();

    Builder kmsKeyId(String kmsKeyId);

    String kmsKeyId();

    Builder encryptionAlgorithm(EncryptionAlgorithmSpec encryptionAlgorithm);

    EncryptionAlgorithmSpec encryptionAlgorithm();

    Builder kmsClient(KmsClient kmsClient);

    KmsClient kmsClient();

    Builder grantTokens(List<String> grantTokens);

    List<String> grantTokens();

    CreateAwsKmsRsaKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected ByteBuffer publicKey;

    protected String kmsKeyId;

    protected EncryptionAlgorithmSpec encryptionAlgorithm;

    protected KmsClient kmsClient;

    protected List<String> grantTokens;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsRsaKeyringInput model) {
      this.publicKey = model.publicKey();
      this.kmsKeyId = model.kmsKeyId();
      this.encryptionAlgorithm = model.encryptionAlgorithm();
      this.kmsClient = model.kmsClient();
      this.grantTokens = model.grantTokens();
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public Builder kmsKeyId(String kmsKeyId) {
      this.kmsKeyId = kmsKeyId;
      return this;
    }

    public String kmsKeyId() {
      return this.kmsKeyId;
    }

    public Builder encryptionAlgorithm(EncryptionAlgorithmSpec encryptionAlgorithm) {
      this.encryptionAlgorithm = encryptionAlgorithm;
      return this;
    }

    public EncryptionAlgorithmSpec encryptionAlgorithm() {
      return this.encryptionAlgorithm;
    }

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsRsaKeyringInput build() {
      if (Objects.isNull(this.kmsKeyId()))  {
        throw new IllegalArgumentException("Missing value for required field `kmsKeyId`");
      }
      if (Objects.isNull(this.encryptionAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `encryptionAlgorithm`");
      }
      return new CreateAwsKmsRsaKeyringInput(this);
    }
  }
}
