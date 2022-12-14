// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class AESEncryptInput {
  private final AES_GCM encAlg;

  private final ByteBuffer iv;

  private final ByteBuffer key;

  private final ByteBuffer msg;

  private final ByteBuffer aad;

  protected AESEncryptInput(BuilderImpl builder) {
    this.encAlg = builder.encAlg();
    this.iv = builder.iv();
    this.key = builder.key();
    this.msg = builder.msg();
    this.aad = builder.aad();
  }

  public AES_GCM encAlg() {
    return this.encAlg;
  }

  public ByteBuffer iv() {
    return this.iv;
  }

  public ByteBuffer key() {
    return this.key;
  }

  public ByteBuffer msg() {
    return this.msg;
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

    Builder iv(ByteBuffer iv);

    ByteBuffer iv();

    Builder key(ByteBuffer key);

    ByteBuffer key();

    Builder msg(ByteBuffer msg);

    ByteBuffer msg();

    Builder aad(ByteBuffer aad);

    ByteBuffer aad();

    AESEncryptInput build();
  }

  static class BuilderImpl implements Builder {
    protected AES_GCM encAlg;

    protected ByteBuffer iv;

    protected ByteBuffer key;

    protected ByteBuffer msg;

    protected ByteBuffer aad;

    protected BuilderImpl() {
    }

    protected BuilderImpl(AESEncryptInput model) {
      this.encAlg = model.encAlg();
      this.iv = model.iv();
      this.key = model.key();
      this.msg = model.msg();
      this.aad = model.aad();
    }

    public Builder encAlg(AES_GCM encAlg) {
      this.encAlg = encAlg;
      return this;
    }

    public AES_GCM encAlg() {
      return this.encAlg;
    }

    public Builder iv(ByteBuffer iv) {
      this.iv = iv;
      return this;
    }

    public ByteBuffer iv() {
      return this.iv;
    }

    public Builder key(ByteBuffer key) {
      this.key = key;
      return this;
    }

    public ByteBuffer key() {
      return this.key;
    }

    public Builder msg(ByteBuffer msg) {
      this.msg = msg;
      return this;
    }

    public ByteBuffer msg() {
      return this.msg;
    }

    public Builder aad(ByteBuffer aad) {
      this.aad = aad;
      return this;
    }

    public ByteBuffer aad() {
      return this.aad;
    }

    public AESEncryptInput build() {
      if (Objects.isNull(this.encAlg()))  {
        throw new IllegalArgumentException("Missing value for required field `encAlg`");
      }
      if (Objects.isNull(this.iv()))  {
        throw new IllegalArgumentException("Missing value for required field `iv`");
      }
      if (Objects.isNull(this.key()))  {
        throw new IllegalArgumentException("Missing value for required field `key`");
      }
      if (Objects.isNull(this.msg()))  {
        throw new IllegalArgumentException("Missing value for required field `msg`");
      }
      if (Objects.isNull(this.aad()))  {
        throw new IllegalArgumentException("Missing value for required field `aad`");
      }
      return new AESEncryptInput(this);
    }
  }
}
