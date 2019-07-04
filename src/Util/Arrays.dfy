module {:extern "Arrays"} Arrays {
  class {:extern "Array"} Array {
    //  C# Array.Copy method
    static method {:extern "copy"} copy<T>(source: array<T>, length: nat) returns (dest: array<T>)
      requires length <= source.Length
      ensures dest.Length == length
      ensures fresh(dest) && forall i :: 0 <= i < length ==> dest[i] == source[i]

    //  C# Array.CopyTo method
    static method {:extern "copyTo"} copyTo<T>(source: array<T>, dest: array<T>, offset: nat)
      modifies dest
      requires offset + source.Length <= dest.Length
      ensures dest.Length == old(dest.Length)
      ensures dest[..] == old(dest[..offset]) + source[..] + old(dest[offset+source.Length..])
      ensures source[..] == old(source[..])

  }
}