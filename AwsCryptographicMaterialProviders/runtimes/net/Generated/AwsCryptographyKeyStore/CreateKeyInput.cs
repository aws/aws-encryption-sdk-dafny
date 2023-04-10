// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.KeyStore; namespace AWS.Cryptography.KeyStore {
 public class CreateKeyInput {
 private string _awsKmsKeyArn ;
 public string AwsKmsKeyArn {
 get { return this._awsKmsKeyArn; }
 set { this._awsKmsKeyArn = value; }
}
 public bool IsSetAwsKmsKeyArn () {
 return this._awsKmsKeyArn != null;
}
 public void Validate() {
 if (!IsSetAwsKmsKeyArn()) throw new System.ArgumentException("Missing value for required property 'AwsKmsKeyArn'");

}
}
}
