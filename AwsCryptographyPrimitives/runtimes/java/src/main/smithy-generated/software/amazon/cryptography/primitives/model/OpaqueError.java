// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

public class OpaqueError extends NativeError {
  private final Object obj;

  protected OpaqueError(BuilderImpl builder) {
    super(builder);
    this.obj = builder.obj();
  }

  @Override
  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Object obj() {
    return this.obj;
  }

  public interface Builder extends NativeError.Builder {
    Builder message(String message);

    Builder cause(Throwable cause);

    Builder obj(Object obj);

    Object obj();

    OpaqueError build();
  }

  static class BuilderImpl extends NativeError.BuilderImpl implements Builder {
    protected Object obj;

    protected BuilderImpl() {
    }

    protected BuilderImpl(OpaqueError model) {
      super(model);
      this.obj = model.obj();
    }

    public Builder obj(Object obj) {
      this.obj = obj;
      return this;
    }

    public Object obj() {
      return this.obj;
    }

    @Override
    public Builder message(String message) {
      super.message(message);
      return this;
    }

    @Override
    public Builder cause(Throwable cause) {
      super.cause(cause);
      return this;
    }

    @Override
    public OpaqueError build() {
      return new OpaqueError(this);
    }
  }
}
