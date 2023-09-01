// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestCreateEsdkClient {
    import Types = AwsCryptographyEncryptionSdkTypes
    import mplTypes = AwsCryptographyMaterialProvidersTypes
    import EncryptionSdk

    method {:test} TestClientCreation() {
        var defaultConfig := EncryptionSdk.DefaultAwsEncryptionSdkConfig();
        
        var esdk :- expect EncryptionSdk.ESDK(config := defaultConfig);
        
        expect esdk.config.commitmentPolicy == defaultConfig.commitmentPolicy.value;
        expect esdk.config.maxEncryptedDataKeys == defaultConfig.maxEncryptedDataKeys;
    }
}