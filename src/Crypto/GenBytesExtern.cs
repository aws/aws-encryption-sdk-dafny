using System;
using System.Security.Cryptography;

namespace RNGWrap {
    public partial class GenBytesClass {
        private RandomNumberGenerator rng;

        public GenBytesClass() { rng = RandomNumberGenerator.Create(); }

        public Dafny.Sequence<byte> GenUniformSeq(int i) {
            byte[] z = new byte[i];
            rng.GetBytes(z);
            return new Dafny.Sequence<byte>(z);

        }

        public void GenUniformArray(int i, out byte[] z) {
            z = new byte[i];
            rng.GetBytes(z);
        }
    }
}