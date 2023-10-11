// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProviders;
namespace AWS.Cryptography.MaterialProviders
{
  public class InitializeDecryptionMaterialsInput
  {
    private AWS.Cryptography.MaterialProviders.AlgorithmSuiteId _algorithmSuiteId;
    private System.Collections.Generic.Dictionary<string, string> _encryptionContext;
    private System.Collections.Generic.List<string> _requiredEncryptionContextKeys;
    public AWS.Cryptography.MaterialProviders.AlgorithmSuiteId AlgorithmSuiteId
    {
      get { return this._algorithmSuiteId; }
      set { this._algorithmSuiteId = value; }
    }
    public bool IsSetAlgorithmSuiteId()
    {
      return this._algorithmSuiteId != null;
    }
    public System.Collections.Generic.Dictionary<string, string> EncryptionContext
    {
      get { return this._encryptionContext; }
      set { this._encryptionContext = value; }
    }
    public bool IsSetEncryptionContext()
    {
      return this._encryptionContext != null;
    }
    public System.Collections.Generic.List<string> RequiredEncryptionContextKeys
    {
      get { return this._requiredEncryptionContextKeys; }
      set { this._requiredEncryptionContextKeys = value; }
    }
    public bool IsSetRequiredEncryptionContextKeys()
    {
      return this._requiredEncryptionContextKeys != null;
    }
    public void Validate()
    {
      if (!IsSetAlgorithmSuiteId()) throw new System.ArgumentException("Missing value for required property 'AlgorithmSuiteId'");
      if (!IsSetEncryptionContext()) throw new System.ArgumentException("Missing value for required property 'EncryptionContext'");
      if (!IsSetRequiredEncryptionContextKeys()) throw new System.ArgumentException("Missing value for required property 'RequiredEncryptionContextKeys'");

    }
  }
}
