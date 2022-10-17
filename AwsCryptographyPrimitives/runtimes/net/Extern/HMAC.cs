// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;

using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using _IDigestAlgorithm = Dafny.Aws.Cryptography.Primitives.Types._IDigestAlgorithm;
using Error_Opaque = Dafny.Aws.Cryptography.Primitives.Types.Error_Opaque;

namespace HMAC {

    public partial class HMac {

        private Org.BouncyCastle.Crypto.Macs.HMac hmac;

        public HMac(_IDigestAlgorithm digest) {
            Org.BouncyCastle.Crypto.IDigest bouncyCastleDigest;
            if (digest.is_SHA__1) {
                bouncyCastleDigest = new Org.BouncyCastle.Crypto.Digests.Sha1Digest();
            } else if(digest.is_SHA__256) {
                bouncyCastleDigest = new Org.BouncyCastle.Crypto.Digests.Sha256Digest();
            } else if(digest.is_SHA__384) {
                bouncyCastleDigest = new Org.BouncyCastle.Crypto.Digests.Sha384Digest();
            } else if(digest.is_SHA__512) {
                bouncyCastleDigest = new Org.BouncyCastle.Crypto.Digests.Sha512Digest();
            } else
            {
                throw new System.Exception(String.Format("Unsupported digest: {0}", digest.ToString()));
            }
            hmac = new Org.BouncyCastle.Crypto.Macs.HMac(bouncyCastleDigest);
        }

        public void Init(ibyteseq input) {
            // KeyParameter/ Init should not mutate input, but this is safer than using input.Elements directly
            byte[] elemCopy = (byte[]) input.Elements.Clone();
            var keyParams = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(elemCopy);
            hmac.Init(keyParams);
            // elemCopy may contain sensitive info; zeroize it to reduce time this lives in memory
            Array.Clear(elemCopy, 0, elemCopy.Length);
            elemCopy = null;
        }

        public void BlockUpdate(ibyteseq input) {
            // BlockUpdate should not mutate input, but this is safer than using input.Elements directly
            byte[] elemCopy = (byte[]) input.Elements.Clone();
            hmac.BlockUpdate(elemCopy, 0, elemCopy.Length);
            // elemCopy may contain sensitive info; zeroize it to reduce time this lives in memory
            Array.Clear(elemCopy, 0, elemCopy.Length);
            elemCopy = null;
        }

        public ibyteseq GetResult() {
            byte[] output = new byte[hmac.GetMacSize()];
            hmac.DoFinal(output, 0);
            return byteseq.FromArray(output);
        }
    }
}
