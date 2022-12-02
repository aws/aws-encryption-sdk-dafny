package HKDF_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import dafny.DafnySequence;

public class HMAC {
    public static class HMac {
        private String hmac;
        public HMac(DigestAlgorithm digest) {
            hmac = digest.toString();
        }

        public void Init(DafnySequence<? extends Byte> salt) {
        }

        public void BlockUpdate(DafnySequence<? extends Byte> ikm) {
        }

        public DafnySequence<? extends Byte> GetResult() {
            return null;
        }
    }
}
