// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProviders;
namespace AWS.Cryptography.MaterialProviders
{
  public class CollectionOfErrors : Exception
  {
    public readonly System.Collections.Generic.List<Exception> list;
    public CollectionOfErrors(System.Collections.Generic.List<Exception> list) : base("CollectionOfErrors") { this.list = list; }
    public CollectionOfErrors() : base("CollectionOfErrors") { this.list = new System.Collections.Generic.List<Exception>(); }
  }

}
