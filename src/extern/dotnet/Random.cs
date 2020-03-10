using System;
using System.Security.Cryptography;

namespace Random {
    public partial class __default {
        // Normally we would include a try/catch block in any extern method,
        // to catch failures. In this case though, GetBytes will only error
        // if `z` is Null, which should never happen.
        public static Dafny.Sequence<byte> ExternGenerateBytes(int i) {
            RandomNumberGenerator rng = RandomNumberGenerator.Create();
            byte[] z = new byte[i];
            rng.GetBytes(z);
            return Dafny.Sequence<byte>.FromArray(z);
        }
    }
}
