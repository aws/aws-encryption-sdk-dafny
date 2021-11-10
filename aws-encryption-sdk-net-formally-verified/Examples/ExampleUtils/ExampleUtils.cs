// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.IO;
using System.Text;

namespace ExampleUtils {
    class ExampleUtils {
        static public MemoryStream GetPlaintextStream() {
            return new MemoryStream(Encoding.UTF8.GetBytes(
                        "Lorem ipsum dolor sit amet, consectetur adipiscing elit."
                        ));
        }
    }
}
