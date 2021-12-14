include "../../../libraries/src/Collections/Sequences/Seq.dfy"

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../StandardLibrary/UInt.dfy"

include "Unicode.dfy"
include "Utf8EncodingForm.dfy"

// TODO this should refine an abstract UnicodeEncodingScheme module,
// but defining such a module seems impossible so long as dafny-lang/dafny#1639 is unresolved.
// See <https://github.com/dafny-lang/dafny/issues/1639>.
/**
 * The Unicode encoding scheme that serializes a UTF-8 code unit sequence in exactly the same order as the code unit
 * sequence itself.

 * Because the UTF-8 encoding form already deals in ordered byte sequences, the UTF-8 encoding scheme is trivial. The
 * byte ordering is already obvious and completely defined by the UTF-8 code unit sequence itself. The UTF-8
 * encoding scheme is defined merely for completeness of the Unicode character encoding model.

 * (Section 3.10 D95)
 */
module Utf8EncodingScheme {
  import Seq

  import opened Wrappers = StandardLibrary.Wrappers
  import UInt = StandardLibrary.UInt

  import Unicode
  import Utf8EncodingForm

  type byte = UInt.uint8

  /**
   * Returns the byte serialization of the given code unit sequence.
   */
  function method Serialize(s: Utf8EncodingForm.CodeUnitSeq): (b: seq<byte>)
  {
    Seq.Map(c => c as byte, s)
  }

  /**
   * Returns the code unit sequence that serializes to the given byte sequence.
   */
  function method Deserialize(b: seq<byte>): (s: Utf8EncodingForm.CodeUnitSeq)
  {
    Seq.Map(b => b as Utf8EncodingForm.CodeUnit, b)
  }

  /**
   * Serializing a code unit sequence and then deserializing the result, yields the original code unit sequence.
   */
  lemma LemmaSerializeDeserialize(s: Utf8EncodingForm.CodeUnitSeq)
    ensures Deserialize(Serialize(s)) == s
  {}

  /**
   * Deserializing a byte sequence and then serializing the result, yields the original byte sequence.
   */
  lemma LemmaDeserializeSerialize(b: seq<byte>)
    ensures Serialize(Deserialize(b)) == b
  {}
}
