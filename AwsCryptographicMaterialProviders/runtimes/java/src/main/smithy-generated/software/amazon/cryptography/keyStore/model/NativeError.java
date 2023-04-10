// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

public class NativeError extends RuntimeException {
  protected NativeError(BuilderImpl builder) {
    super(messageFromBuilder(builder), builder.cause());
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
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

  static class BuilderImpl implements Builder {
    protected String message;

    protected Throwable cause;

    protected BuilderImpl() {
    }

    protected BuilderImpl(NativeError model) {
      this.cause = model.getCause();
      this.message = model.getMessage();
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

    public NativeError build() {
      return new NativeError(this);
    }
  }

  public interface Builder {
    Builder message(String message);

    String message();

    Builder cause(Throwable cause);

    Throwable cause();

    NativeError build();
  }
}
