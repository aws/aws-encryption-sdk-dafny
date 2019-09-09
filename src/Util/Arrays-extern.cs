using System;
using System.Numerics;

namespace Arrays {

  using Utils;
  public partial class Array {
    public static T[] copy<T>(T[] source, BigInteger length) {
      T[] dest = new T[Util.BigIntegerToInt(length)];
      System.Array.Copy(source, dest, Util.BigIntegerToInt(length));
      return dest;
    }
    public static void copyTo<T>(T[] source, T[] dest, BigInteger offset) {
      source.CopyTo(dest, Util.BigIntegerToInt(offset)); 
    }
  }
}