package BouncyCastleCryptoMac;

import BouncyCastleCryptoMac.CipherParameters;
import Digests.HMAC_ALGORITHM;
import Utils.AlgorithmNotSupportedException;
import Utils.Util;
import dafny.DafnySequence;
import dafny.UByte;

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
      org.bouncycastle.crypto.params.KeyParameter bcKeyParameter = new org.bouncycastle.crypto.params.KeyParameter(Util.uBytesToBytes(ps.key));
      bcHMac.init(bcKeyParameter);
    }
  }

  @Override
  public void reset() {
    bcHMac.reset();
  }

  @Override
  public void updateSingle(UByte input) {
    bcHMac.update(input.byteValue());
  }

  @Override
  public void update(UByte[] input , BigInteger inOff, BigInteger len) {
    bcHMac.update(Util.uBytesToBytes(input), Util.bigIntegerToInt(inOff), Util.bigIntegerToInt(len));
  }

  @Override
  public BigInteger doFinal(UByte[] output, BigInteger outOff) {
    byte[] bytes = new byte[output.length - Util.bigIntegerToInt(outOff)];
    BigInteger ans = BigInteger.valueOf(bcHMac.doFinal(bytes, 0));
    System.arraycopy(Util.bytesToUBytes(bytes), 0, output, outOff.intValue(), bytes.length);
    return ans;
  }

  @Override
  public HMAC_ALGORITHM getUnderlyingDigest() {
    // TODO
    throw new UnsupportedOperationException();
  }
}
