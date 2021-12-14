// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../libraries/src/Collections/Sequences/Seq.dfy"
include "../../../libraries/src/Functions.dfy"

include "../../StandardLibrary/StandardLibrary.dfy"

include "Unicode.dfy"

/**
 * A Unicode encoding form assigns each Unicode scalar value to a unique code unit sequence.
 *
 * A concrete `EncodingForm` MUST define the following:
 *  - The type `CodeUnit`.
 *  - The predicate `IsMinimalWellFormedCodeUnitSubsequence`, which defines the set of encodings of scalar values,
 *    known as "minimal well-formed code unit subsequences".
 *  - The function `SplitPrefixMinimalWellFormedCodeUnitSubsequence`, which defines the algorithm by which to parse
 *    a minimal well-formed code unit subsequence from the beginning of a code unit sequence.
 *  - The function `EncodeScalarValue`, which defines the mapping from scalar values to minimal well-formed code unit
 *    subsequences.
 *  - The function `DecodeMinimalWellFormedCodeUnitSubsequence`, which defines the mapping from minimal well-formed
 *    code unit subsequences to scalar values.
 */
abstract module UnicodeEncodingForm {
  import Functions
  import Seq

  import opened Wrappers = StandardLibrary.Wrappers

  import Unicode

  type CodeUnitSeq = seq<CodeUnit>
  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *

  //
  // Begin abstract items.
  //

  /**
    * A code unit is the minimal bit combination that can represent a unit of encoded text for processing or
    * interchange. (Section 3.9 D77.)
    */
  type CodeUnit

  /**
    * A well-formed Unicode code unit sequence that maps to a single Unicode scalar value.
    * (Section 3.9 D85a.)
    */
  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==>
      && |s| > 0
      && forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|

  /**
    * Returns the shortest prefix of `s` that is a minimal well-formed code unit subsequence,
    * or None if there is no such prefix.
    */
  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==>
      && maybePrefix.Some?
    ensures maybePrefix.Some? ==>
      && var prefix := maybePrefix.Extract();
      && 0 < |prefix| <= |s|
      && prefix == s[..|prefix|]
      && forall i | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])

  /**
    * Returns the minimal well-formed code unit subsequence that this encoding form assigns to the given scalar value.
    */
  // This needs to be injective by the Unicode standard. I'm not sure how to require this.
  // Maybe functions that rely on injectivity should simply state that reliance in their preconditions?
  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)

  /**
    * Returns the scalar value that this encoding form assigns to the given minimal well-formed code unit subsequence.
    */
  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    ensures EncodeScalarValue(v) == m

  //
  // End abstract items.
  //
}
