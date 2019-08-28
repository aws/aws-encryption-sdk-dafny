include "UInt.dfy"

module {:extern "STL"} StandardLibrary {
  datatype Option<T> = None | Some(get: T)

  datatype Result<T> = Success(value : T) | Failure(error : string)
}
