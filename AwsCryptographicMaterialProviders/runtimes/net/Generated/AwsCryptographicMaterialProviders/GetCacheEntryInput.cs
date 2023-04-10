// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class GetCacheEntryInput {
 private System.IO.MemoryStream _identifier ;
 private long? _bytesUsed ;
 public System.IO.MemoryStream Identifier {
 get { return this._identifier; }
 set { this._identifier = value; }
}
 public bool IsSetIdentifier () {
 return this._identifier != null;
}
 public long BytesUsed {
 get { return this._bytesUsed.GetValueOrDefault(); }
 set { this._bytesUsed = value; }
}
 public bool IsSetBytesUsed () {
 return this._bytesUsed.HasValue;
}
 public void Validate() {
 if (!IsSetIdentifier()) throw new System.ArgumentException("Missing value for required property 'Identifier'");

}
}
}
