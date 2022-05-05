// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Numerics;

namespace TimeUtil {
    public class Time {
        public static ulong CurrentRelativeTime() {
            var timespan = DateTime.Now - DateTime.MinValue;
            return (ulong)timespan.TotalSeconds;
        }
    }
}
