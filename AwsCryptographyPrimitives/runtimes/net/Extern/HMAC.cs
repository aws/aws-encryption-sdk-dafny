// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Collections.Immutable;
using Wrappers_Compile;
using software.amazon.cryptography.primitives.internaldafny.types;
using Org.BouncyCastle.Math;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using _IDigestAlgorithm = software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;

namespace HMAC {

    public partial class __default {
        public static _IResult<ibyteseq, _IError> Digest(_IHMacInput input)
        {
            var maybeHmac = HMac.Build(input.dtor_digestAlgorithm);

            if (maybeHmac.is_Failure)
            {
                return (maybeHmac).PropagateFailure<Dafny.ISequence<byte>>();
            }
            var hmac = maybeHmac.Extract();
            hmac.Init(input.dtor_key);
            hmac.BlockUpdate(input.dtor_message);
            return Result<ibyteseq, _IError>.create_Success(hmac.GetResult());
        }
    }

    public partial class HMac {

        private Org.BouncyCastle.Crypto.Macs.HMac hmac;

        public static _IResult<HMac, _IError> Build(_IDigestAlgorithm digest)
        {
            try
            {
                return Result<HMac, _IError>.create_Success(new HMac(digest));
            }
            catch (Exception ex)
            {
                return Wrappers_Compile.Result<HMac, _IError>
                    .create_Failure(AWS.Cryptography.Primitives.TypeConversion.ToDafny_CommonError(ex));
            }
            
        }

        public HMac(_IDigestAlgorithm digest) {
            Org.BouncyCastle.Crypto.IDigest bouncyCastleDigest;
            if(digest.is_SHA__256) {
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
