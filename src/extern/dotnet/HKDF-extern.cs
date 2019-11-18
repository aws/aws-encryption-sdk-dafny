using System;
using System.Numerics;

namespace Utils {

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

  public class AlgorithmNotSupportedException : Exception
  {
      public AlgorithmNotSupportedException(string message)
          : base(message)
      {
      }
  }
}


namespace BouncyCastleCryptoMac {

  using Utils;
  public partial class HMac {

    private Org.BouncyCastle.Crypto.Macs.HMac bcHMac;

    public HMac(Digests.HMAC_ALGORITHM algorithm) {
      Org.BouncyCastle.Crypto.IDigest digest;
      if(algorithm.is_HmacSHA256) {
        digest = new Org.BouncyCastle.Crypto.Digests.Sha256Digest();
        bcHMac = new Org.BouncyCastle.Crypto.Macs.HMac(digest);
      } else if(algorithm.is_HmacSHA384) {
        digest = new Org.BouncyCastle.Crypto.Digests.Sha384Digest();
        bcHMac = new Org.BouncyCastle.Crypto.Macs.HMac(digest);
      } else {
        throw new AlgorithmNotSupportedException(algorithm.ToString() + " not supported.");
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

    public BigInteger doFinal(byte[] output, BigInteger outOff) {
      return new BigInteger(bcHMac.DoFinal(output, Util.BigIntegerToInt(outOff)));
    }

    public Org.BouncyCastle.Crypto.IDigest getUnderlyingDigest() {
      return bcHMac.GetUnderlyingDigest();
    }

  }
}
