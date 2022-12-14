// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.primitives.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class HkdfExtractInput {
  private final DigestAlgorithm digestAlgorithm;

  private final ByteBuffer salt;

  private final ByteBuffer ikm;

  protected HkdfExtractInput(BuilderImpl builder) {
    this.digestAlgorithm = builder.digestAlgorithm();
    this.salt = builder.salt();
    this.ikm = builder.ikm();
  }

  public DigestAlgorithm digestAlgorithm() {
    return this.digestAlgorithm;
  }

  public ByteBuffer salt() {
    return this.salt;
  }

  public ByteBuffer ikm() {
    return this.ikm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder digestAlgorithm(DigestAlgorithm digestAlgorithm);

    DigestAlgorithm digestAlgorithm();

    Builder salt(ByteBuffer salt);

    ByteBuffer salt();

    Builder ikm(ByteBuffer ikm);

    ByteBuffer ikm();

    HkdfExtractInput build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm digestAlgorithm;

    protected ByteBuffer salt;

    protected ByteBuffer ikm;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HkdfExtractInput model) {
      this.digestAlgorithm = model.digestAlgorithm();
      this.salt = model.salt();
      this.ikm = model.ikm();
    }

    public Builder digestAlgorithm(DigestAlgorithm digestAlgorithm) {
      this.digestAlgorithm = digestAlgorithm;
      return this;
    }

    public DigestAlgorithm digestAlgorithm() {
      return this.digestAlgorithm;
    }

    public Builder salt(ByteBuffer salt) {
      this.salt = salt;
      return this;
    }

    public ByteBuffer salt() {
      return this.salt;
    }

    public Builder ikm(ByteBuffer ikm) {
      this.ikm = ikm;
      return this;
    }

    public ByteBuffer ikm() {
      return this.ikm;
    }

    public HkdfExtractInput build() {
      if (Objects.isNull(this.digestAlgorithm()))  {
        throw new IllegalArgumentException("Missing value for required field `digestAlgorithm`");
      }
      if (Objects.isNull(this.ikm()))  {
        throw new IllegalArgumentException("Missing value for required field `ikm`");
      }
      return new HkdfExtractInput(this);
    }
  }
}
