package Arrays;

import dafny.Type;

import java.math.BigInteger;

public class Array {
  private Array() { }

  public static <T> Object copy(Type<T> t, Object source, BigInteger length) {
    assert t.arrayType().isInstance(source);

    if (length.intValue() == t.getArrayLength(source)) {
      return t.cloneArray(source);
    } else {
      Object dest = t.newArray(length.intValue());
      t.copyArrayTo(source, 0, dest, 0, length.intValue());
      return dest;
    }
  }
  public static <T> void copyTo(Type<T> t, Object source, Object dest, BigInteger offset) {
    t.copyArrayTo(source, 0, dest, offset.intValue(), t.getArrayLength(source));
  }
}
