// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package Random_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.Error;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

import java.security.SecureRandom;

public class ExternRandom {
    public static class __default {

        //= compliance/data-format/message-header.txt#2.5.1.6
        //# While
        //# implementations cannot guarantee complete uniqueness, implementations
        //# MUST use a good source of randomness when generating messages IDs in
        //# order to make the chance of duplicate IDs negligible.
        private static final SecureRandom RND = new SecureRandom();

        public static Result<DafnySequence<? extends Byte>, Error> GenerateBytes(final int len) {
            try {
                // We should revisit if there are limits on amount of
                // bytes we can request with different crypto providers
                final byte[] result = new byte[len];
                RND.nextBytes(result);
                return Result.create_Success(DafnySequence.fromBytes(result));
            } catch (Exception e) {
                return Result.create_Failure(ToDafny.Error(OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build()));
            }
        }
    }
}
