module {:extern "STL"} StandardLibrary {
  datatype Option<T> = None | Some(get: T)

  datatype Result<T> = Ok(get : T) | Err(err : string)
}