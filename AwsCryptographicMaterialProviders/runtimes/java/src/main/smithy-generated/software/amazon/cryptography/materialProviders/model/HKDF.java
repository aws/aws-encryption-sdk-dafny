// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;
import software.amazon.cryptography.primitives.model.DigestAlgorithm;

public class HKDF {
  private final DigestAlgorithm hmac;

  private final int saltLength;

  private final int inputKeyLength;

  private final int outputKeyLength;

  protected HKDF(BuilderImpl builder) {
    this.hmac = builder.hmac();
    this.saltLength = builder.saltLength();
    this.inputKeyLength = builder.inputKeyLength();
    this.outputKeyLength = builder.outputKeyLength();
  }

  public DigestAlgorithm hmac() {
    return this.hmac;
  }

  public int saltLength() {
    return this.saltLength;
  }

  public int inputKeyLength() {
    return this.inputKeyLength;
  }

  public int outputKeyLength() {
    return this.outputKeyLength;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder hmac(DigestAlgorithm hmac);

    DigestAlgorithm hmac();

    Builder saltLength(int saltLength);

    int saltLength();

    Builder inputKeyLength(int inputKeyLength);

    int inputKeyLength();

    Builder outputKeyLength(int outputKeyLength);

    int outputKeyLength();

    HKDF build();
  }

  static class BuilderImpl implements Builder {
    protected DigestAlgorithm hmac;

    protected int saltLength;

    private boolean _saltLengthSet = false;

    protected int inputKeyLength;

    private boolean _inputKeyLengthSet = false;

    protected int outputKeyLength;

    private boolean _outputKeyLengthSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(HKDF model) {
      this.hmac = model.hmac();
      this.saltLength = model.saltLength();
      this._saltLengthSet = true;
      this.inputKeyLength = model.inputKeyLength();
      this._inputKeyLengthSet = true;
      this.outputKeyLength = model.outputKeyLength();
      this._outputKeyLengthSet = true;
    }

    public Builder hmac(DigestAlgorithm hmac) {
      this.hmac = hmac;
      return this;
    }

    public DigestAlgorithm hmac() {
      return this.hmac;
    }

    public Builder saltLength(int saltLength) {
      this.saltLength = saltLength;
      this._saltLengthSet = true;
      return this;
    }

    public int saltLength() {
      return this.saltLength;
    }

    public Builder inputKeyLength(int inputKeyLength) {
      this.inputKeyLength = inputKeyLength;
      this._inputKeyLengthSet = true;
      return this;
    }

    public int inputKeyLength() {
      return this.inputKeyLength;
    }

    public Builder outputKeyLength(int outputKeyLength) {
      this.outputKeyLength = outputKeyLength;
      this._outputKeyLengthSet = true;
      return this;
    }

    public int outputKeyLength() {
      return this.outputKeyLength;
    }

    public HKDF build() {
      if (Objects.isNull(this.hmac()))  {
        throw new IllegalArgumentException("Missing value for required field `hmac`");
      }
      if (!this._saltLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `saltLength`");
      }
      if (this._saltLengthSet && this.saltLength() < 0) {
        throw new IllegalArgumentException("`saltLength` must be greater than or equal to 0");
      }
      if (!this._inputKeyLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `inputKeyLength`");
      }
      if (this._inputKeyLengthSet && this.inputKeyLength() < 1) {
        throw new IllegalArgumentException("`inputKeyLength` must be greater than or equal to 1");
      }
      if (this._inputKeyLengthSet && this.inputKeyLength() > 32) {
        throw new IllegalArgumentException("`inputKeyLength` must be less than or equal to 32.");
      }
      if (!this._outputKeyLengthSet) {
        throw new IllegalArgumentException("Missing value for required field `outputKeyLength`");
      }
      if (this._outputKeyLengthSet && this.outputKeyLength() < 1) {
        throw new IllegalArgumentException("`outputKeyLength` must be greater than or equal to 1");
      }
      if (this._outputKeyLengthSet && this.outputKeyLength() > 32) {
        throw new IllegalArgumentException("`outputKeyLength` must be less than or equal to 32.");
      }
      return new HKDF(this);
    }
  }
}
