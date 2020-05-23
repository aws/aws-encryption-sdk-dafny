package BouncyCastleCryptoMac;

import Digests.HMAC_ALGORITHM;
import Utils.AlgorithmNotSupportedException;
import Utils.Util;
import dafny.DafnySequence;

import java.math.BigInteger;

public class HMac extends _ExternBase_HMac {

  private org.bouncycastle.crypto.macs.HMac bcHMac;

  public HMac(Digests.HMAC_ALGORITHM algorithm) {
    org.bouncycastle.crypto.Digest digest;
    if(algorithm.is_HmacSHA256()) {
      digest = new org.bouncycastle.crypto.digests.SHA256Digest();
      bcHMac = new org.bouncycastle.crypto.macs.HMac(digest);
    } else if(algorithm.is_HmacSHA384()) {
      digest = new org.bouncycastle.crypto.digests.SHA384Digest();
      bcHMac = new org.bouncycastle.crypto.macs.HMac(digest);
    } else {
      throw new AlgorithmNotSupportedException(algorithm.toString() + " not supported.");
    }
  }

  @Override
  public DafnySequence<Character> getAlgorithmName() {
    return DafnySequence.asString(bcHMac.getAlgorithmName());
  }

  @Override
  public BigInteger getMacSize() {
    return BigInteger.valueOf(bcHMac.getMacSize());
  }

  @Override
  public void init(CipherParameters ps) {
    if(ps.is_KeyParameter()) {
      org.bouncycastle.crypto.params.KeyParameter bcKeyParameter = new org.bouncycastle.crypto.params.KeyParameter(ps.key);
      bcHMac.init(bcKeyParameter);
    }
  }

  @Override
  public void reset() {
    bcHMac.reset();
  }

  @Override
  public void updateSingle(byte input) {
    bcHMac.update(input);
  }

  @Override
  public void update(byte[] input , BigInteger inOff, BigInteger len) {
    bcHMac.update(input, Util.bigIntegerToInt(inOff), Util.bigIntegerToInt(len));
  }

  @Override
  public BigInteger doFinal(byte[] output, BigInteger outOff) {
    byte[] bytes = new byte[output.length - Util.bigIntegerToInt(outOff)];
    BigInteger ans = BigInteger.valueOf(bcHMac.doFinal(bytes, 0));
    System.arraycopy(bytes, 0, output, outOff.intValue(), bytes.length);
    return ans;
  }

  @Override
  public HMAC_ALGORITHM getUnderlyingDigest() {
    // TODO
    throw new UnsupportedOperationException();
  }
}
