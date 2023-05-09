// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Security;
using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using _IError = software.amazon.cryptography.primitives.internaldafny.types._IError;
using Error_Opaque = software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;

namespace AesKdfCtr {
   public partial class __default {
        public static _IResult<ibyteseq, _IError> AesKdfCtrStream (
            ibyteseq iv,
            ibyteseq key,
	    uint length
        )
        {
            var keyBytes = key.Elements;
            var nonceBytes = iv.Elements;
            var ciphertext = new byte[length];
            var msg = new byte[length];

            try
            {
                var param = new ParametersWithIV(new KeyParameter(keyBytes), nonceBytes);
                var cipher = CipherUtilities.GetCipher("AES/CTR");
                cipher.Init(true, param);
                var len = cipher.ProcessBytes(msg, 0, msg.Length, ciphertext, 0);
                cipher.DoFinal(ciphertext, len);
                return Result<ibyteseq, _IError>.create_Success(
                    byteseq.FromArray(ciphertext));
            }
            catch (Exception ex)
            {
                return Wrappers_Compile.Result<ibyteseq, _IError>
                    .create_Failure(new Error_Opaque(ex));
            }
        }
    }
}
