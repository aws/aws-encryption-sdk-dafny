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
    public class DiscoveryFilter
    {
        public string Region { get; private set; }
        public string Partition { get; private set; }

        public static IDiscoveryFilterBuilder Builder()
        {
            return new DiscoveryFilterBuilder();
        }

        public void Validate()
        {
        }

        private class DiscoveryFilterBuilder : IDiscoveryFilterBuilder
        {
            private string Region;
            private string Partition;

            public IDiscoveryFilterBuilder WithRegion(string value)
            {
                Region = value;
                return this;
            }

            public IDiscoveryFilterBuilder WithPartition(string value)
            {
                Partition = value;
                return this;
            }

            public DiscoveryFilter Build()
            {
                if (Region == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "region"));
                }

                if (Partition == null)
                {
                    throw new InvalidOperationException(
                        String.Format("No value set for required field {0}", "partition"));
                }

                return new DiscoveryFilter
                {
                    Region = (string) Region, Partition = (string) Partition,
                };
            }
        }
    }

    public interface IDiscoveryFilterBuilder
    {
        IDiscoveryFilterBuilder WithRegion(string value);
        IDiscoveryFilterBuilder WithPartition(string value);
        DiscoveryFilter Build();
    }
}
