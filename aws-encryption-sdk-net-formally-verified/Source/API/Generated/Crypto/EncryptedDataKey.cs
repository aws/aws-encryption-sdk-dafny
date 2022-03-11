// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
 using Aws.Crypto;
 using
 Aws.Crypto
 ; namespace Aws.Crypto {
 public class EncryptedDataKey {
 private string _keyProviderId ;
 private string _keyProviderInfo ;
 private System.IO.MemoryStream _ciphertext ;
 public string KeyProviderId {
 get { return this._keyProviderId; }
 set { this._keyProviderId = value; }
}
 internal bool IsSetKeyProviderId () {
 return this._keyProviderId != null;
}
 public string KeyProviderInfo {
 get { return this._keyProviderInfo; }
 set { this._keyProviderInfo = value; }
}
 internal bool IsSetKeyProviderInfo () {
 return this._keyProviderInfo != null;
}
 public System.IO.MemoryStream Ciphertext {
 get { return this._ciphertext; }
 set { this._ciphertext = value; }
}
 internal bool IsSetCiphertext () {
 return this._ciphertext != null;
}
 public void Validate() {
 if (!IsSetKeyProviderId()) throw new System.ArgumentException("Missing value for required member 'keyProviderId'");
 if (!IsSetKeyProviderInfo()) throw new System.ArgumentException("Missing value for required member 'keyProviderInfo'");
 if (!IsSetCiphertext()) throw new System.ArgumentException("Missing value for required member 'ciphertext'");

}
}
}
