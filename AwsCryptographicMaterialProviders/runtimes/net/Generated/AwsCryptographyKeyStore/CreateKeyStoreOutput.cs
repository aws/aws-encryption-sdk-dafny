// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class CreateKeyStoreOutput {
 private string _tableArn ;
 public string TableArn {
 get { return this._tableArn; }
 set { this._tableArn = value; }
}
 public bool IsSetTableArn () {
 return this._tableArn != null;
}
 public void Validate() {
 if (!IsSetTableArn()) throw new System.ArgumentException("Missing value for required property 'TableArn'");

}
}
}
