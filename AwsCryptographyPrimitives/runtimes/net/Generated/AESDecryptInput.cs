// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.Primitives; namespace AWS.Cryptography.Primitives {
 public class AESDecryptInput {
 private AWS.Cryptography.Primitives.AES_GCM _encAlg ;
 private System.IO.MemoryStream _key ;
 private System.IO.MemoryStream _cipherTxt ;
 private System.IO.MemoryStream _authTag ;
 private System.IO.MemoryStream _iv ;
 private System.IO.MemoryStream _aad ;
 public AWS.Cryptography.Primitives.AES_GCM EncAlg {
 get { return this._encAlg; }
 set { this._encAlg = value; }
}
 public bool IsSetEncAlg () {
 return this._encAlg != null;
}
 public System.IO.MemoryStream Key {
 get { return this._key; }
 set { this._key = value; }
}
 public bool IsSetKey () {
 return this._key != null;
}
 public System.IO.MemoryStream CipherTxt {
 get { return this._cipherTxt; }
 set { this._cipherTxt = value; }
}
 public bool IsSetCipherTxt () {
 return this._cipherTxt != null;
}
 public System.IO.MemoryStream AuthTag {
 get { return this._authTag; }
 set { this._authTag = value; }
}
 public bool IsSetAuthTag () {
 return this._authTag != null;
}
 public System.IO.MemoryStream Iv {
 get { return this._iv; }
 set { this._iv = value; }
}
 public bool IsSetIv () {
 return this._iv != null;
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
 if (!IsSetKey()) throw new System.ArgumentException("Missing value for required property 'Key'");
 if (!IsSetCipherTxt()) throw new System.ArgumentException("Missing value for required property 'CipherTxt'");
 if (!IsSetAuthTag()) throw new System.ArgumentException("Missing value for required property 'AuthTag'");
 if (!IsSetIv()) throw new System.ArgumentException("Missing value for required property 'Iv'");
 if (!IsSetAad()) throw new System.ArgumentException("Missing value for required property 'Aad'");

}
}
}
