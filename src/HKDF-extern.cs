using System;
using System.Numerics;

public static class Util {
  public static int BigIntegerToInt(BigInteger x) {
    try {
      return (int) x;
    } catch(OverflowException e) {
      // TODO: error handling
      Console.WriteLine(e.ToString());
      throw e;
    }
  }
}

namespace Arrays {
  public partial class Array {
    public static void copy<T>(T[] source, BigInteger length, out T[] dest) {
      dest = new T[Util.BigIntegerToInt(length)];
      System.Array.Copy(source, dest, Util.BigIntegerToInt(length));
    }
    public static void copyTo<T>(T[] source, T[] dest, BigInteger offset) {
      source.CopyTo(dest, Util.BigIntegerToInt(offset)); 
    }
  }
}


namespace BouncyCastleCryptoMac {

  using Org.BouncyCastle.Crypto;
  public partial class HMac {

    private Org.BouncyCastle.Crypto.Macs.HMac bcHMac;

    public HMac(Digests.HMAC_ALGORITHM algorithm) {
      IDigest digest;
      if(algorithm.is_HmacSHA256) {
        digest = new Org.BouncyCastle.Crypto.Digests.Sha256Digest();
        bcHMac = new Org.BouncyCastle.Crypto.Macs.HMac(digest);
      }
      if(algorithm.is_HmacSHA384) {
        digest = new Org.BouncyCastle.Crypto.Digests.Sha384Digest();
        bcHMac = new Org.BouncyCastle.Crypto.Macs.HMac(digest);
      }
    }

    public Dafny.Sequence<char> getAlgorithmName() {
      return Dafny.Sequence<char>.FromString(bcHMac.AlgorithmName);
    }

    public BigInteger getMacSize() {
      return new BigInteger(bcHMac.GetMacSize());
    }
    
    public void init(CipherParameters ps) {
      if(ps.is_KeyParameter) {
        var bcKeyParameter = new Org.BouncyCastle.Crypto.Parameters.KeyParameter(ps.key);
        bcHMac.Init(bcKeyParameter);
      }
    }

    public void reset() {
      bcHMac.Reset();
    }
 
    public void updateSingle(byte input) {
      bcHMac.Update(input);
    }
 
    public void update(byte[] input , BigInteger inOff, BigInteger len) {
      bcHMac.BlockUpdate(input, Util.BigIntegerToInt(inOff), Util.BigIntegerToInt(len));
    }
 
    public void doFinal(byte[] output, BigInteger outOff, out BigInteger retVal) {
      retVal = new BigInteger(bcHMac.DoFinal(output, Util.BigIntegerToInt(outOff)));
    }

    public Org.BouncyCastle.Crypto.IDigest getUnderlyingDigest() {
      return bcHMac.GetUnderlyingDigest();
    }

  }
}