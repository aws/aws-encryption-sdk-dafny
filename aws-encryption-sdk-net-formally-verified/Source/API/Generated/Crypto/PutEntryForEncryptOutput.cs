// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-03T00:21:59.652135

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class PutEntryForEncryptOutput
    {
        public static IPutEntryForEncryptOutputBuilder Builder()
        {
            return new PutEntryForEncryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class PutEntryForEncryptOutputBuilder : IPutEntryForEncryptOutputBuilder
        {
            public PutEntryForEncryptOutput Build()
            {
                return new PutEntryForEncryptOutput
                {
                };
            }
        }
    }

    public interface IPutEntryForEncryptOutputBuilder
    {
        PutEntryForEncryptOutput Build();
    }
}
