// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.util.List;

public class CollectionOfErrors extends NativeError {
  private final List<NativeError> list;

  protected CollectionOfErrors(BuilderImpl builder) {
    super(builder);
    this.list = builder.list();
  }

  public List<NativeError> list() {
    return this.list;
  }

  @Override
  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder extends NativeError.Builder {
    Builder message(String message);

    Builder cause(Throwable cause);

    Builder list(List<NativeError> list);

    List<NativeError> list();

    CollectionOfErrors build();
  }

  static class BuilderImpl extends NativeError.BuilderImpl implements Builder {
    protected List<NativeError> list;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CollectionOfErrors model) {
      super(model);
      this.list = model.list();
    }

    public Builder list(List<NativeError> list) {
      this.list = list;
      return this;
    }

    public List<NativeError> list() {
      return this.list;
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
    public CollectionOfErrors build() {
      return new CollectionOfErrors(this);
    }
  }
}
