// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Numerics;
using Microsoft.VisualBasic;

namespace Time {

    public partial class __default {
        public static ulong CurrentRelativeTime()
        {
            var timespan = DateTime.Now - DateTime.MinValue;
            return (ulong) timespan.TotalSeconds;
        }
    }
}