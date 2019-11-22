package Arrays;

import java.math.BigInteger;

public class Array {
  private Array() { }

  public static <T> T[] copy(String td, T[] source, BigInteger length) {
    if (length.intValue() == source.length) {
      return source.clone();
    } else {
      @SuppressWarnings("unchecked")
      T[] dest = (T[]) java.lang.reflect.Array.newInstance(
              source.getClass().getComponentType(), length.intValue());
      System.arraycopy(source, 0, dest, 0, length.intValue());
      return dest;
    }
  }
  public static <T> void copyTo(T[] source, T[] dest, BigInteger offset) {
    System.arraycopy(source, 0, dest, offset.intValue(), source.length);
  }
}
