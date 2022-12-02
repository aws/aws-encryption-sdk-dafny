package HMAC;

import Dafny.Aws.Cryptography.Primitives.Types.DigestAlgorithm;
import HKDF_Compile.HMAC;

public class HMac extends HMAC.HMac {

    public HMac(DigestAlgorithm digestAlgorithm) {
        super(digestAlgorithm);
    }
}
