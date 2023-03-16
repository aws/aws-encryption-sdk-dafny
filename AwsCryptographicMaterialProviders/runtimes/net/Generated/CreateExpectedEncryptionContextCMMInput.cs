// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProviders;
namespace AWS.Cryptography.MaterialProviders
{
  public class CreateExpectedEncryptionContextCMMInput
  {
    private AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager _underlyingCMM;
    private AWS.Cryptography.MaterialProviders.IKeyring _keyring;
    private System.Collections.Generic.List<string> _requiredEncryptionContextKeys;
    public AWS.Cryptography.MaterialProviders.ICryptographicMaterialsManager UnderlyingCMM
    {
      get { return this._underlyingCMM; }
      set { this._underlyingCMM = value; }
    }
    public bool IsSetUnderlyingCMM()
    {
      return this._underlyingCMM != null;
    }
    public AWS.Cryptography.MaterialProviders.IKeyring Keyring
    {
      get { return this._keyring; }
      set { this._keyring = value; }
    }
    public bool IsSetKeyring()
    {
      return this._keyring != null;
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
      if (!IsSetRequiredEncryptionContextKeys()) throw new System.ArgumentException("Missing value for required property 'RequiredEncryptionContextKeys'");

    }
  }
}
