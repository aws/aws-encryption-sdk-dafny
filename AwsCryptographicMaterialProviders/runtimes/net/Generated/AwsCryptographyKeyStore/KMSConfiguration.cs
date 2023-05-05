// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class KMSConfiguration {
 private string _kmsKeyArn ;
 public string KmsKeyArn {
 get { return this._kmsKeyArn; }
 set { this._kmsKeyArn = value; }
}
 public bool IsSetKmsKeyArn () {
 return this._kmsKeyArn != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetKmsKeyArn()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
