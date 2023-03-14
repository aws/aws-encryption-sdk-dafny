// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProviders;
namespace AWS.Cryptography.MaterialProviders
{
  public class CreateCryptographicMaterialsCacheInput
  {
    private int? _entryCapacity;
    private int? _entryPruningTailSize;
    public int EntryCapacity
    {
      get { return this._entryCapacity.GetValueOrDefault(); }
      set { this._entryCapacity = value; }
    }
    public bool IsSetEntryCapacity()
    {
      return this._entryCapacity.HasValue;
    }
    public int EntryPruningTailSize
    {
      get { return this._entryPruningTailSize.GetValueOrDefault(); }
      set { this._entryPruningTailSize = value; }
    }
    public bool IsSetEntryPruningTailSize()
    {
      return this._entryPruningTailSize.HasValue;
    }
    public void Validate()
    {
      if (!IsSetEntryCapacity()) throw new System.ArgumentException("Missing value for required property 'EntryCapacity'");

    }
  }
}
