// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DeleteCacheEntryInput {
 private System.IO.MemoryStream _identifier ;
 public System.IO.MemoryStream Identifier {
 get { return this._identifier; }
 set { this._identifier = value; }
}
 public bool IsSetIdentifier () {
 return this._identifier != null;
}
 public void Validate() {
 if (!IsSetIdentifier()) throw new System.ArgumentException("Missing value for required property 'Identifier'");

}
}
}
