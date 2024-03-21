// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.EncryptionSDK;
namespace AWS.Cryptography.EncryptionSDK
{
    public class OpaqueError : Exception
    {
        public readonly object obj;
        public OpaqueError(Exception ex) : base("OpaqueError:", ex) { this.obj = ex; }
        public OpaqueError() : base("Unknown Unexpected Error") { }
        public OpaqueError(object obj) : base(obj is Exception ? "OpaqueError:" : "Opaque obj is not an Exception.", obj as Exception) { this.obj = obj; }
    }

}
