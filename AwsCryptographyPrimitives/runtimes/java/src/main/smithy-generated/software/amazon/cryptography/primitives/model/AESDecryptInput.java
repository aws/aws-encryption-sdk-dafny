// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AESDecryptInput {
  private final AES_GCM encAlg;

  private final ByteBuffer key;

  private final ByteBuffer cipherTxt;

  private final ByteBuffer authTag;

  private final ByteBuffer iv;

  private final ByteBuffer aad;

  protected AESDecryptInput(BuilderImpl builder) {
    this.encAlg = builder.encAlg();
    this.key = builder.key();
    this.cipherTxt = builder.cipherTxt();
    this.authTag = builder.authTag();
    this.iv = builder.iv();
    this.aad = builder.aad();
  }

  public AES_GCM encAlg() {
    return this.encAlg;
  }

  public ByteBuffer key() {
    return this.key;
  }

  public ByteBuffer cipherTxt() {
    return this.cipherTxt;
  }

  public ByteBuffer authTag() {
    return this.authTag;
  }

  public ByteBuffer iv() {
    return this.iv;
  }

  public ByteBuffer aad() {
    return this.aad;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder encAlg(AES_GCM encAlg);

    AES_GCM encAlg();

    Builder key(ByteBuffer key);

    ByteBuffer key();

    Builder cipherTxt(ByteBuffer cipherTxt);

    ByteBuffer cipherTxt();

    Builder authTag(ByteBuffer authTag);

    ByteBuffer authTag();

    Builder iv(ByteBuffer iv);

    ByteBuffer iv();

    Builder aad(ByteBuffer aad);

    ByteBuffer aad();

    AESDecryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected AES_GCM encAlg;

    protected ByteBuffer key;

    protected ByteBuffer cipherTxt;

    protected ByteBuffer authTag;

    protected ByteBuffer iv;

    protected ByteBuffer aad;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AESDecryptInput model) {
      this.encAlg = model.encAlg();
      this.key = model.key();
      this.cipherTxt = model.cipherTxt();
      this.authTag = model.authTag();
      this.iv = model.iv();
      this.aad = model.aad();
    }

    public Builder encAlg(AES_GCM encAlg) {
      this.encAlg = encAlg;
      return this;
    }

    public AES_GCM encAlg() {
      return this.encAlg;
    }

    public Builder key(ByteBuffer key) {
      this.key = key;
      return this;
    }

    public ByteBuffer key() {
      return this.key;
    }

    public Builder cipherTxt(ByteBuffer cipherTxt) {
      this.cipherTxt = cipherTxt;
      return this;
    }

    public ByteBuffer cipherTxt() {
      return this.cipherTxt;
    }

    public Builder authTag(ByteBuffer authTag) {
      this.authTag = authTag;
      return this;
    }

    public ByteBuffer authTag() {
      return this.authTag;
    }

    public Builder iv(ByteBuffer iv) {
      this.iv = iv;
      return this;
    }

    public ByteBuffer iv() {
      return this.iv;
    }

    public Builder aad(ByteBuffer aad) {
      this.aad = aad;
      return this;
    }

    public ByteBuffer aad() {
      return this.aad;
    }

    public AESDecryptInput build() {
      if (Objects.isNull(this.encAlg()))  {
        throw new IllegalArgumentException("Missing value for required field `encAlg`");
      }
      if (Objects.isNull(this.key()))  {
        throw new IllegalArgumentException("Missing value for required field `key`");
      }
      if (Objects.isNull(this.cipherTxt()))  {
        throw new IllegalArgumentException("Missing value for required field `cipherTxt`");
      }
      if (Objects.isNull(this.authTag()))  {
        throw new IllegalArgumentException("Missing value for required field `authTag`");
      }
      if (Objects.isNull(this.iv()))  {
        throw new IllegalArgumentException("Missing value for required field `iv`");
      }
      if (Objects.isNull(this.aad()))  {
        throw new IllegalArgumentException("Missing value for required field `aad`");
      }
      return new AESDecryptInput(this);
    }
  }
}
