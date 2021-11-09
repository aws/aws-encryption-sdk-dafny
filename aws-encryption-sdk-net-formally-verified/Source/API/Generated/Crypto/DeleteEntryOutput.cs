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
    public class DeleteEntryOutput
    {
        public static IDeleteEntryOutputBuilder Builder()
        {
            return new DeleteEntryOutputBuilder();
        }

        public void Validate()
        {
        }

        private class DeleteEntryOutputBuilder : IDeleteEntryOutputBuilder
        {
            public DeleteEntryOutput Build()
            {
                return new DeleteEntryOutput
                {
                };
            }
        }
    }

    public interface IDeleteEntryOutputBuilder
    {
        DeleteEntryOutput Build();
    }
}
