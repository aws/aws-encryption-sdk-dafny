// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;

public class CollectionOfErrors extends RuntimeException {
  private final List<RuntimeException> list;

  protected CollectionOfErrors(BuilderImpl builder) {
    super(messageFromBuilder(builder), builder.cause());
    this.list = builder.list();
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

  public List<RuntimeException> list() {
    return this.list;
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

    Builder list(List<RuntimeException> list);

    List<RuntimeException> list();

    CollectionOfErrors build();
  }

  static class BuilderImpl implements Builder {
    protected String message;

    protected Throwable cause;

    protected List<RuntimeException> list;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CollectionOfErrors model) {
      this.cause = model.getCause();
      this.message = model.getMessage();
      this.list = model.list();
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

    public Builder list(List<RuntimeException> list) {
      this.list = list;
      return this;
    }

    public List<RuntimeException> list() {
      return this.list;
    }

    public CollectionOfErrors build() {
      return new CollectionOfErrors(this);
    }
  }
}
