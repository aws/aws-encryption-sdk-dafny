// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class HKDF {
 private AWS.Cryptography.Primitives.DigestAlgorithm _hmac ;
 private int? _saltLength ;
 private int? _inputKeyLength ;
 private int? _outputKeyLength ;
 public AWS.Cryptography.Primitives.DigestAlgorithm Hmac {
 get { return this._hmac; }
 set { this._hmac = value; }
}
 public bool IsSetHmac () {
 return this._hmac != null;
}
 public int SaltLength {
 get { return this._saltLength.GetValueOrDefault(); }
 set { this._saltLength = value; }
}
 public bool IsSetSaltLength () {
 return this._saltLength.HasValue;
}
 public int InputKeyLength {
 get { return this._inputKeyLength.GetValueOrDefault(); }
 set { this._inputKeyLength = value; }
}
 public bool IsSetInputKeyLength () {
 return this._inputKeyLength.HasValue;
}
 public int OutputKeyLength {
 get { return this._outputKeyLength.GetValueOrDefault(); }
 set { this._outputKeyLength = value; }
}
 public bool IsSetOutputKeyLength () {
 return this._outputKeyLength.HasValue;
}
 public void Validate() {
 if (!IsSetHmac()) throw new System.ArgumentException("Missing value for required property 'Hmac'");
 if (!IsSetSaltLength()) throw new System.ArgumentException("Missing value for required property 'SaltLength'");
 if (!IsSetInputKeyLength()) throw new System.ArgumentException("Missing value for required property 'InputKeyLength'");
 if (!IsSetOutputKeyLength()) throw new System.ArgumentException("Missing value for required property 'OutputKeyLength'");

}
}
}
