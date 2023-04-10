// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateMultiKeyringInput {
 private AWS.Cryptography.MaterialProviders.IKeyring _generator ;
 private System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.IKeyring> _childKeyrings ;
 public AWS.Cryptography.MaterialProviders.IKeyring Generator {
 get { return this._generator; }
 set { this._generator = value; }
}
 public bool IsSetGenerator () {
 return this._generator != null;
}
 public System.Collections.Generic.List<AWS.Cryptography.MaterialProviders.IKeyring> ChildKeyrings {
 get { return this._childKeyrings; }
 set { this._childKeyrings = value; }
}
 public bool IsSetChildKeyrings () {
 return this._childKeyrings != null;
}
 public void Validate() {
 if (!IsSetChildKeyrings()) throw new System.ArgumentException("Missing value for required property 'ChildKeyrings'");

}
}
}
