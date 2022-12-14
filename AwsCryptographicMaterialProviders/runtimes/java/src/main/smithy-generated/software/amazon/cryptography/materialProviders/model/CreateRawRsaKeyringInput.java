// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class CreateRawRsaKeyringInput {
  private final String keyNamespace;

  private final String keyName;

  private final PaddingScheme paddingScheme;

  private final ByteBuffer publicKey;

  private final ByteBuffer privateKey;

  protected CreateRawRsaKeyringInput(BuilderImpl builder) {
    this.keyNamespace = builder.keyNamespace();
    this.keyName = builder.keyName();
    this.paddingScheme = builder.paddingScheme();
    this.publicKey = builder.publicKey();
    this.privateKey = builder.privateKey();
  }

  public String keyNamespace() {
    return this.keyNamespace;
  }

  public String keyName() {
    return this.keyName;
  }

  public PaddingScheme paddingScheme() {
    return this.paddingScheme;
  }

  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  public ByteBuffer privateKey() {
    return this.privateKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyNamespace(String keyNamespace);

    String keyNamespace();

    Builder keyName(String keyName);

    String keyName();

    Builder paddingScheme(PaddingScheme paddingScheme);

    PaddingScheme paddingScheme();

    Builder publicKey(ByteBuffer publicKey);

    ByteBuffer publicKey();

    Builder privateKey(ByteBuffer privateKey);

    ByteBuffer privateKey();

    CreateRawRsaKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String keyNamespace;

    protected String keyName;

    protected PaddingScheme paddingScheme;

    protected ByteBuffer publicKey;

    protected ByteBuffer privateKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateRawRsaKeyringInput model) {
      this.keyNamespace = model.keyNamespace();
      this.keyName = model.keyName();
      this.paddingScheme = model.paddingScheme();
      this.publicKey = model.publicKey();
      this.privateKey = model.privateKey();
    }

    public Builder keyNamespace(String keyNamespace) {
      this.keyNamespace = keyNamespace;
      return this;
    }

    public String keyNamespace() {
      return this.keyNamespace;
    }

    public Builder keyName(String keyName) {
      this.keyName = keyName;
      return this;
    }

    public String keyName() {
      return this.keyName;
    }

    public Builder paddingScheme(PaddingScheme paddingScheme) {
      this.paddingScheme = paddingScheme;
      return this;
    }

    public PaddingScheme paddingScheme() {
      return this.paddingScheme;
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public Builder privateKey(ByteBuffer privateKey) {
      this.privateKey = privateKey;
      return this;
    }

    public ByteBuffer privateKey() {
      return this.privateKey;
    }

    public CreateRawRsaKeyringInput build() {
      if (Objects.isNull(this.keyNamespace()))  {
        throw new IllegalArgumentException("Missing value for required field `keyNamespace`");
      }
      if (Objects.isNull(this.keyName()))  {
        throw new IllegalArgumentException("Missing value for required field `keyName`");
      }
      if (Objects.isNull(this.paddingScheme()))  {
        throw new IllegalArgumentException("Missing value for required field `paddingScheme`");
      }
      return new CreateRawRsaKeyringInput(this);
    }
  }
}
