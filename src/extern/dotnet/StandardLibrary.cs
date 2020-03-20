namespace STL {

  public partial class __default {
    public static Option<T> Cast<T>(object x) where T : class {
      var casted = x as T;
      if (casted != null) {
        return Option<T>.create_Some(casted);
      } else {
        return Option<T>.create_None();
      }
    }

    public static Dafny.ISequence<char> FromExternalString(string s) {
      return DafnyFFI.DafnyStringFromString(s);
    }
  }
}