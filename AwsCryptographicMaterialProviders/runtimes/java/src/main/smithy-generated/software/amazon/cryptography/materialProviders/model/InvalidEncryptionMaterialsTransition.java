// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.Objects;

public class InvalidEncryptionMaterialsTransition extends RuntimeException {
  protected InvalidEncryptionMaterialsTransition(BuilderImpl builder) {
    super(messageFromBuilder(builder), builder.cause());
  }

  private static String messageFromBuilder(Builder builder) {
    if (builder.message() != null) {
      return builder.message();
    }
    if (builder.cause() != null) {
      return builder.cause().getMessage();
    }
    return null;
  }

  public String message() {
    return this.getMessage();
  }

  public Throwable cause() {
    return this.getCause();
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder message(String message);

    String message();

    Builder cause(Throwable cause);

    Throwable cause();

    InvalidEncryptionMaterialsTransition build();
  }

  static class BuilderImpl implements Builder {
    protected String message;

    protected Throwable cause;

    protected BuilderImpl() {
    }

    protected BuilderImpl(InvalidEncryptionMaterialsTransition model) {
      this.message = model.message();
      this.cause = model.cause();
    }

    public Builder message(String message) {
      this.message = message;
      return this;
    }

    public String message() {
      return this.message;
    }

    public Builder cause(Throwable cause) {
      this.cause = cause;
      return this;
    }

    public Throwable cause() {
      return this.cause;
    }

    public InvalidEncryptionMaterialsTransition build() {
      if (Objects.isNull(this.message()))  {
        throw new IllegalArgumentException("Missing value for required field `message`");
      }
      return new InvalidEncryptionMaterialsTransition(this);
    }
  }
}
