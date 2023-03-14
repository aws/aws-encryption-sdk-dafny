// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Test vector projects just run as a CLI
// So all the tests are in the Main.
// By creating a single file here,
// it is easy to kick off a test run.
include "../src/Index.dfy"

module TestWrappedMaterialProvidersMain {
  import WrappedMaterialProvidersMain

  method {:test} TestCheckKeyrings() {
    WrappedMaterialProvidersMain.CheckKeyrings();
  }
}
