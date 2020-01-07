package Arrays;

import dafny.Type;

import java.math.BigInteger;

public class Array {
  private Array() { }

  public static <T> dafny.Array<T> copy(Type<T> t, dafny.Array<T> source, BigInteger length) {
    if (length.intValue() == source.length) {
      return source.clone();
    } else {
      dafny.Array<T> dest = t.newArray(length.intValue());
      source.copy(0, dest, 0, length.intValue());
      return dest;
    }
  }
  public static <T> void copyTo(Type<T> t, dafny.Array<T> source, dafny.Array<T> dest, BigInteger offset) {
    source.copy(0, dest, offset.intValue(), source.length);
  }
}
