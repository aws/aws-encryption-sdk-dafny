// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateRawAesKeyringInput {
 private string _keyNamespace ;
 private string _keyName ;
 private System.IO.MemoryStream _wrappingKey ;
 private AWS.Cryptography.MaterialProviders.AesWrappingAlg _wrappingAlg ;
 public string KeyNamespace {
 get { return this._keyNamespace; }
 set { this._keyNamespace = value; }
}
 public bool IsSetKeyNamespace () {
 return this._keyNamespace != null;
}
 public string KeyName {
 get { return this._keyName; }
 set { this._keyName = value; }
}
 public bool IsSetKeyName () {
 return this._keyName != null;
}
 public System.IO.MemoryStream WrappingKey {
 get { return this._wrappingKey; }
 set { this._wrappingKey = value; }
}
 public bool IsSetWrappingKey () {
 return this._wrappingKey != null;
}
 public AWS.Cryptography.MaterialProviders.AesWrappingAlg WrappingAlg {
 get { return this._wrappingAlg; }
 set { this._wrappingAlg = value; }
}
 public bool IsSetWrappingAlg () {
 return this._wrappingAlg != null;
}
 public void Validate() {
 if (!IsSetKeyNamespace()) throw new System.ArgumentException("Missing value for required property 'KeyNamespace'");
 if (!IsSetKeyName()) throw new System.ArgumentException("Missing value for required property 'KeyName'");
 if (!IsSetWrappingKey()) throw new System.ArgumentException("Missing value for required property 'WrappingKey'");
 if (!IsSetWrappingAlg()) throw new System.ArgumentException("Missing value for required property 'WrappingAlg'");

}
}
}
