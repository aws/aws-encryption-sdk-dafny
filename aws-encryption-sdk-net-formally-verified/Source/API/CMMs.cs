// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// using CMMDefs;
using DefaultCMMDef;
// using CachingCMMDef;
// using KeyringDefs;
using System.Numerics;

namespace AWSEncryptionSDK
{
    // public class CMMs
    // {
    //     public static CMM MakeDefaultCMM(Keyring keyring)
    //     {
    //         DefaultCMM result = new DefaultCMM();
    //         // TODO: The Dafny constructor shouldn't be directly callable from C# code!
    //         // In particular, this isn't checking for a null keyring.
    //         result.OfKeyring(keyring);
    //         return result;
    //     }
    //
    //     public static CMM MakeCachingCMM(CMM cmm, ulong secondsToLiveLimit, ulong bytesLimit, ulong messagesLimit)
    //     {
    //         var result = new CachingCMM();
    //         // TODO: The Dafny constructor shouldn't be directly callable from C# code!
    //         // In particular, this isn't checking for a null cmm or a positive secondsToLiveLimit.
    //         result.WithLimits(cmm, new BigInteger(secondsToLiveLimit), bytesLimit, messagesLimit);
    //         return result;
    //     }
    // }
}
