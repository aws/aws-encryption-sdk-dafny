// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Generated at 2021-11-17T11:30:48.725424

using System;
using Aws.Crypto;
using
    Aws.Crypto
    ;

namespace Aws.Crypto
{
    public class PutEntryForDecryptOutput
    {
        public static IPutEntryForDecryptOutputBuilder Builder()
        {
            return new PutEntryForDecryptOutputBuilder();
        }

        public void Validate()
        {
        }

        private class PutEntryForDecryptOutputBuilder : IPutEntryForDecryptOutputBuilder
        {
            public PutEntryForDecryptOutput Build()
            {
                return new PutEntryForDecryptOutput
                {
                };
            }
        }
    }

    public interface IPutEntryForDecryptOutputBuilder
    {
        PutEntryForDecryptOutput Build();
    }
}