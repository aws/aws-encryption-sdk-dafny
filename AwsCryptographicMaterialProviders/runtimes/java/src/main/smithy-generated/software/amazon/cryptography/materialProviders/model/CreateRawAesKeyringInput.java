// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class CreateRawAesKeyringInput {
  private final String keyNamespace;

  private final String keyName;

  private final ByteBuffer wrappingKey;

  private final AesWrappingAlg wrappingAlg;

  protected CreateRawAesKeyringInput(BuilderImpl builder) {
    this.keyNamespace = builder.keyNamespace();
    this.keyName = builder.keyName();
    this.wrappingKey = builder.wrappingKey();
    this.wrappingAlg = builder.wrappingAlg();
  }

  public String keyNamespace() {
    return this.keyNamespace;
  }

  public String keyName() {
    return this.keyName;
  }

  public ByteBuffer wrappingKey() {
    return this.wrappingKey;
  }

  public AesWrappingAlg wrappingAlg() {
    return this.wrappingAlg;
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

    Builder wrappingKey(ByteBuffer wrappingKey);

    ByteBuffer wrappingKey();

    Builder wrappingAlg(AesWrappingAlg wrappingAlg);

    AesWrappingAlg wrappingAlg();

    CreateRawAesKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String keyNamespace;

    protected String keyName;

    protected ByteBuffer wrappingKey;

    protected AesWrappingAlg wrappingAlg;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateRawAesKeyringInput model) {
      this.keyNamespace = model.keyNamespace();
      this.keyName = model.keyName();
      this.wrappingKey = model.wrappingKey();
      this.wrappingAlg = model.wrappingAlg();
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

    public Builder wrappingKey(ByteBuffer wrappingKey) {
      this.wrappingKey = wrappingKey;
      return this;
    }

    public ByteBuffer wrappingKey() {
      return this.wrappingKey;
    }

    public Builder wrappingAlg(AesWrappingAlg wrappingAlg) {
      this.wrappingAlg = wrappingAlg;
      return this;
    }

    public AesWrappingAlg wrappingAlg() {
      return this.wrappingAlg;
    }

    public CreateRawAesKeyringInput build() {
      if (Objects.isNull(this.keyNamespace()))  {
        throw new IllegalArgumentException("Missing value for required field `keyNamespace`");
      }
      if (Objects.isNull(this.keyName()))  {
        throw new IllegalArgumentException("Missing value for required field `keyName`");
      }
      if (Objects.isNull(this.wrappingKey()))  {
        throw new IllegalArgumentException("Missing value for required field `wrappingKey`");
      }
      if (Objects.isNull(this.wrappingAlg()))  {
        throw new IllegalArgumentException("Missing value for required field `wrappingAlg`");
      }
      return new CreateRawAesKeyringInput(this);
    }
  }
}
