// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

public class OpaqueError extends RuntimeException {
  private final Object obj;

  protected OpaqueError(BuilderImpl builder) {
    super(messageFromBuilder(builder), builder.cause());
    this.obj = builder.obj();
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

  public Object obj() {
    return this.obj;
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

    Builder obj(Object obj);

    Object obj();

    OpaqueError build();
  }

  static class BuilderImpl implements Builder {
    protected String message;

    protected Throwable cause;

    protected Object obj;

    protected BuilderImpl() {
    }

    protected BuilderImpl(OpaqueError model) {
      this.cause = model.getCause();
      this.message = model.getMessage();
      this.obj = model.obj();
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

    public Builder obj(Object obj) {
      this.obj = obj;
      return this;
    }

    public Object obj() {
      return this.obj;
    }

    public OpaqueError build() {
      if (this.obj != null && this.cause == null && this.obj instanceof Throwable) {
        this.cause = (Throwable) this.obj;
      } else if (this.obj == null && this.cause != null) {
        this.obj = this.cause;
      }
      return new OpaqueError(this);
    }
  }
}
