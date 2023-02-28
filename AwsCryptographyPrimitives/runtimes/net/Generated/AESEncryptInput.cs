// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class AESEncryptInput {
 private AWS.Cryptography.Primitives.AES_GCM _encAlg ;
 private System.IO.MemoryStream _iv ;
 private System.IO.MemoryStream _key ;
 private System.IO.MemoryStream _msg ;
 private System.IO.MemoryStream _aad ;
 public AWS.Cryptography.Primitives.AES_GCM EncAlg {
 get { return this._encAlg; }
 set { this._encAlg = value; }
}
 public bool IsSetEncAlg () {
 return this._encAlg != null;
}
 public System.IO.MemoryStream Iv {
 get { return this._iv; }
 set { this._iv = value; }
}
 public bool IsSetIv () {
 return this._iv != null;
}
 public System.IO.MemoryStream Key {
 get { return this._key; }
 set { this._key = value; }
}
 public bool IsSetKey () {
 return this._key != null;
}
 public System.IO.MemoryStream Msg {
 get { return this._msg; }
 set { this._msg = value; }
}
 public bool IsSetMsg () {
 return this._msg != null;
}
 public System.IO.MemoryStream Aad {
 get { return this._aad; }
 set { this._aad = value; }
}
 public bool IsSetAad () {
 return this._aad != null;
}
 public void Validate() {
 if (!IsSetEncAlg()) throw new System.ArgumentException("Missing value for required property 'EncAlg'");
 if (!IsSetIv()) throw new System.ArgumentException("Missing value for required property 'Iv'");
 if (!IsSetKey()) throw new System.ArgumentException("Missing value for required property 'Key'");
 if (!IsSetMsg()) throw new System.ArgumentException("Missing value for required property 'Msg'");
 if (!IsSetAad()) throw new System.ArgumentException("Missing value for required property 'Aad'");

}
}
}
