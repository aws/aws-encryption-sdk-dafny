// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public abstract class AwsCryptographicMaterialProvidersClientFactoryClientBase : IAwsCryptographicMaterialProvidersClientFactory {

 protected AwsCryptographicMaterialProvidersClientFactoryClientBase (  )
 {
 
}
 public Aws.Crypto.IAwsCryptographicMaterialProvidersClient MakeAwsCryptographicMaterialProvidersClient ( Aws.Crypto.AwsCryptographicMaterialProvidersClientConfig input )
 {
 input.Validate(); return _MakeAwsCryptographicMaterialProvidersClient ( input ) ;
}
 protected abstract Aws.Crypto.IAwsCryptographicMaterialProvidersClient _MakeAwsCryptographicMaterialProvidersClient ( Aws.Crypto.AwsCryptographicMaterialProvidersClientConfig input ) ;
}
}
