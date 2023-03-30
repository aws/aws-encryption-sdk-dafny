// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class PutCacheEntryInput {
 private System.IO.MemoryStream _identifier ;
 private AWS.Cryptography.MaterialProviders.Materials _materials ;
 private long? _creationTime ;
 private long? _expiryTime ;
 private int? _messagesUsed ;
 private int? _bytesUsed ;
 public System.IO.MemoryStream Identifier {
 get { return this._identifier; }
 set { this._identifier = value; }
}
 public bool IsSetIdentifier () {
 return this._identifier != null;
}
 public AWS.Cryptography.MaterialProviders.Materials Materials {
 get { return this._materials; }
 set { this._materials = value; }
}
 public bool IsSetMaterials () {
 return this._materials != null;
}
 public long CreationTime {
 get { return this._creationTime.GetValueOrDefault(); }
 set { this._creationTime = value; }
}
 public bool IsSetCreationTime () {
 return this._creationTime.HasValue;
}
 public long ExpiryTime {
 get { return this._expiryTime.GetValueOrDefault(); }
 set { this._expiryTime = value; }
}
 public bool IsSetExpiryTime () {
 return this._expiryTime.HasValue;
}
 public int MessagesUsed {
 get { return this._messagesUsed.GetValueOrDefault(); }
 set { this._messagesUsed = value; }
}
 public bool IsSetMessagesUsed () {
 return this._messagesUsed.HasValue;
}
 public int BytesUsed {
 get { return this._bytesUsed.GetValueOrDefault(); }
 set { this._bytesUsed = value; }
}
 public bool IsSetBytesUsed () {
 return this._bytesUsed.HasValue;
}
 public void Validate() {
 if (!IsSetIdentifier()) throw new System.ArgumentException("Missing value for required property 'Identifier'");
 if (!IsSetMaterials()) throw new System.ArgumentException("Missing value for required property 'Materials'");
 if (!IsSetCreationTime()) throw new System.ArgumentException("Missing value for required property 'CreationTime'");
 if (!IsSetExpiryTime()) throw new System.ArgumentException("Missing value for required property 'ExpiryTime'");

}
}
}
