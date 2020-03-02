namespace STL {

  public partial class __default {
    public static Option<T> As<T>(object x) where T : class {
      var casted = x as T;
      if (casted != null) {
        return Option<T>.create_Some(casted);
      } else {
        return Option<T>.create_None();
      }
    }
  }
}