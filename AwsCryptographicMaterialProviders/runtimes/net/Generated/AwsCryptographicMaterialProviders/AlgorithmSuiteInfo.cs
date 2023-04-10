// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class AlgorithmSuiteInfo {
 private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _id ;
 private System.IO.MemoryStream _binaryId ;
 private int? _messageVersion ;
 private AWS.Cryptography.MaterialProviders.Encrypt _encrypt ;
 private AWS.Cryptography.MaterialProviders.DerivationAlgorithm _kdf ;
 private AWS.Cryptography.MaterialProviders.DerivationAlgorithm _commitment ;
 private AWS.Cryptography.MaterialProviders.SignatureAlgorithm _signature ;
 private AWS.Cryptography.MaterialProviders.SymmetricSignatureAlgorithm _symmetricSignature ;
 private AWS.Cryptography.MaterialProviders.EdkWrappingAlgorithm _edkWrapping ;
 public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId Id {
 get { return this._id; }
 set { this._id = value; }
}
 public bool IsSetId () {
 return this._id != null;
}
 public System.IO.MemoryStream BinaryId {
 get { return this._binaryId; }
 set { this._binaryId = value; }
}
 public bool IsSetBinaryId () {
 return this._binaryId != null;
}
 public int MessageVersion {
 get { return this._messageVersion.GetValueOrDefault(); }
 set { this._messageVersion = value; }
}
 public bool IsSetMessageVersion () {
 return this._messageVersion.HasValue;
}
 public AWS.Cryptography.MaterialProviders.Encrypt Encrypt {
 get { return this._encrypt; }
 set { this._encrypt = value; }
}
 public bool IsSetEncrypt () {
 return this._encrypt != null;
}
 public AWS.Cryptography.MaterialProviders.DerivationAlgorithm Kdf {
 get { return this._kdf; }
 set { this._kdf = value; }
}
 public bool IsSetKdf () {
 return this._kdf != null;
}
 public AWS.Cryptography.MaterialProviders.DerivationAlgorithm Commitment {
 get { return this._commitment; }
 set { this._commitment = value; }
}
 public bool IsSetCommitment () {
 return this._commitment != null;
}
 public AWS.Cryptography.MaterialProviders.SignatureAlgorithm Signature {
 get { return this._signature; }
 set { this._signature = value; }
}
 public bool IsSetSignature () {
 return this._signature != null;
}
 public AWS.Cryptography.MaterialProviders.SymmetricSignatureAlgorithm SymmetricSignature {
 get { return this._symmetricSignature; }
 set { this._symmetricSignature = value; }
}
 public bool IsSetSymmetricSignature () {
 return this._symmetricSignature != null;
}
 public AWS.Cryptography.MaterialProviders.EdkWrappingAlgorithm EdkWrapping {
 get { return this._edkWrapping; }
 set { this._edkWrapping = value; }
}
 public bool IsSetEdkWrapping () {
 return this._edkWrapping != null;
}
 public void Validate() {
 if (!IsSetId()) throw new System.ArgumentException("Missing value for required property 'Id'");
 if (!IsSetBinaryId()) throw new System.ArgumentException("Missing value for required property 'BinaryId'");
 if (!IsSetMessageVersion()) throw new System.ArgumentException("Missing value for required property 'MessageVersion'");
 if (!IsSetEncrypt()) throw new System.ArgumentException("Missing value for required property 'Encrypt'");
 if (!IsSetKdf()) throw new System.ArgumentException("Missing value for required property 'Kdf'");
 if (!IsSetCommitment()) throw new System.ArgumentException("Missing value for required property 'Commitment'");
 if (!IsSetSignature()) throw new System.ArgumentException("Missing value for required property 'Signature'");
 if (!IsSetSymmetricSignature()) throw new System.ArgumentException("Missing value for required property 'SymmetricSignature'");
 if (!IsSetEdkWrapping()) throw new System.ArgumentException("Missing value for required property 'EdkWrapping'");

}
}
}
