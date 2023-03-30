// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DiscoveryFilter {
 private System.Collections.Generic.List<string> _accountIds ;
 private string _partition ;
 public System.Collections.Generic.List<string> AccountIds {
 get { return this._accountIds; }
 set { this._accountIds = value; }
}
 public bool IsSetAccountIds () {
 return this._accountIds != null;
}
 public string Partition {
 get { return this._partition; }
 set { this._partition = value; }
}
 public bool IsSetPartition () {
 return this._partition != null;
}
 public void Validate() {
 if (!IsSetAccountIds()) throw new System.ArgumentException("Missing value for required property 'AccountIds'");
 if (!IsSetPartition()) throw new System.ArgumentException("Missing value for required property 'Partition'");

}
}
}
