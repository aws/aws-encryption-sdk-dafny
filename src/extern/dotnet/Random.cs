using System;
using System.Security.Cryptography;

namespace Random {
  public partial class __default {
    public static Dafny.Sequence<byte> GenerateBytes(int i) {
      RandomNumberGenerator rng = RandomNumberGenerator.Create();
      byte[] z = new byte[i];
      rng.GetBytes(z);
      return new Dafny.Sequence<byte>(z);
    }
  }
}
