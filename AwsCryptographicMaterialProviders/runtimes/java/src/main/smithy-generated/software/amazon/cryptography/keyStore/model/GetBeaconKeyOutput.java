// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keyStore.model;

import java.util.Objects;
import software.amazon.cryptography.materialProviders.model.BeaconKeyMaterials;

public class GetBeaconKeyOutput {
  private final BeaconKeyMaterials beaconKeyMaterials;

  protected GetBeaconKeyOutput(BuilderImpl builder) {
    this.beaconKeyMaterials = builder.beaconKeyMaterials();
  }

  public BeaconKeyMaterials beaconKeyMaterials() {
    return this.beaconKeyMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder beaconKeyMaterials(BeaconKeyMaterials beaconKeyMaterials);

    BeaconKeyMaterials beaconKeyMaterials();

    GetBeaconKeyOutput build();
  }

  static class BuilderImpl implements Builder {
    protected BeaconKeyMaterials beaconKeyMaterials;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBeaconKeyOutput model) {
      this.beaconKeyMaterials = model.beaconKeyMaterials();
    }

    public Builder beaconKeyMaterials(BeaconKeyMaterials beaconKeyMaterials) {
      this.beaconKeyMaterials = beaconKeyMaterials;
      return this;
    }

    public BeaconKeyMaterials beaconKeyMaterials() {
      return this.beaconKeyMaterials;
    }

    public GetBeaconKeyOutput build() {
      if (Objects.isNull(this.beaconKeyMaterials()))  {
        throw new IllegalArgumentException("Missing value for required field `beaconKeyMaterials`");
      }
      return new GetBeaconKeyOutput(this);
    }
  }
}
