// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class CreateKeyOutput {
 private string _branchKeyIdentifier ;
 public string BranchKeyIdentifier {
 get { return this._branchKeyIdentifier; }
 set { this._branchKeyIdentifier = value; }
}
 public bool IsSetBranchKeyIdentifier () {
 return this._branchKeyIdentifier != null;
}
 public void Validate() {
 if (!IsSetBranchKeyIdentifier()) throw new System.ArgumentException("Missing value for required property 'BranchKeyIdentifier'");

}
}
}
