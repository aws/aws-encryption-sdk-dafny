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

        public static Result<DafnySequence<? extends Byte>, Error> GenerateBytes(final int len) {
            try {
                // We should revisit if there are limits on amount of
                // bytes we can request with different crypto providers
                final byte[] result = new byte[len];
                final SecureRandom secureRandom = getSecureRandom();
                secureRandom.nextBytes(result);
                return Result.create_Success(DafnySequence.fromBytes(result));
            } catch (Exception e) {
                return Result.create_Failure(ToDafny.Error(
                        OpaqueError.builder().obj(e).cause(e).message(e.getMessage()).build()));
            }
        }
    }

    // SecureRandom objects can both be expensive to initialize and incur synchronization costs.
    // This allows us to minimize both initializations and keep SecureRandom usage thread local
    // to avoid lock contention.
    private static final ThreadLocal<SecureRandom> LOCAL_RANDOM =
            ThreadLocal.withInitial(() -> {
                //= compliance/data-format/message-header.txt#2.5.1.6
                //# While
                //# implementations cannot guarantee complete uniqueness, implementations
                //# MUST use a good source of randomness when generating messages IDs in
                //# order to make the chance of duplicate IDs negligible.
                final SecureRandom rnd = new SecureRandom();
                rnd.nextBoolean(); // Force seeding
                return rnd;
            });

    public static SecureRandom getSecureRandom() {
        return LOCAL_RANDOM.get();
    }
}
