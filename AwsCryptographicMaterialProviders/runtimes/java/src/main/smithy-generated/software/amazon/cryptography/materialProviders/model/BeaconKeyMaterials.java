// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialProviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Objects;

public class BeaconKeyMaterials {
  private final String beaconKeyIdentifier;

  private final ByteBuffer beaconKey;

  private final List<ByteBuffer> hmacKeys;

  protected BeaconKeyMaterials(BuilderImpl builder) {
    this.beaconKeyIdentifier = builder.beaconKeyIdentifier();
    this.beaconKey = builder.beaconKey();
    this.hmacKeys = builder.hmacKeys();
  }

  public String beaconKeyIdentifier() {
    return this.beaconKeyIdentifier;
  }

  public ByteBuffer beaconKey() {
    return this.beaconKey;
  }

  public List<ByteBuffer> hmacKeys() {
    return this.hmacKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder beaconKeyIdentifier(String beaconKeyIdentifier);

    String beaconKeyIdentifier();

    Builder beaconKey(ByteBuffer beaconKey);

    ByteBuffer beaconKey();

    Builder hmacKeys(List<ByteBuffer> hmacKeys);

    List<ByteBuffer> hmacKeys();

    BeaconKeyMaterials build();
  }

  static class BuilderImpl implements Builder {
    protected String beaconKeyIdentifier;

    protected ByteBuffer beaconKey;

    protected List<ByteBuffer> hmacKeys;

    protected BuilderImpl() {
    }

    protected BuilderImpl(BeaconKeyMaterials model) {
      this.beaconKeyIdentifier = model.beaconKeyIdentifier();
      this.beaconKey = model.beaconKey();
      this.hmacKeys = model.hmacKeys();
    }

    public Builder beaconKeyIdentifier(String beaconKeyIdentifier) {
      this.beaconKeyIdentifier = beaconKeyIdentifier;
      return this;
    }

    public String beaconKeyIdentifier() {
      return this.beaconKeyIdentifier;
    }

    public Builder beaconKey(ByteBuffer beaconKey) {
      this.beaconKey = beaconKey;
      return this;
    }

    public ByteBuffer beaconKey() {
      return this.beaconKey;
    }

    public Builder hmacKeys(List<ByteBuffer> hmacKeys) {
      this.hmacKeys = hmacKeys;
      return this;
    }

    public List<ByteBuffer> hmacKeys() {
      return this.hmacKeys;
    }

    public BeaconKeyMaterials build() {
      if (Objects.isNull(this.beaconKeyIdentifier()))  {
        throw new IllegalArgumentException("Missing value for required field `beaconKeyIdentifier`");
      }
      return new BeaconKeyMaterials(this);
    }
  }
}
