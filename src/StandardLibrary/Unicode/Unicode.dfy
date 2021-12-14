// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../StandardLibrary/StandardLibrary.dfy"
include "../../../libraries/src/Collections/Sequences/Seq.dfy"

// This module implements basic functionality of Unicode 14.0.
module Unicode {
  import opened Wrappers
  import StandardLibrary
  import Seq

  /**
   * Any value in the Unicode codespace (a range of integers from 0 to 10FFFF_16). (Section 3.9 D9-D10)
   */
  type CodePoint = i: bv24 | 0 <= i <= 0x10FFFF

  /**
   * A Unicode code point in the range U+D800 to U+DBFF. (Section 3.8 D71)
   */
  type HighSurrogateCodePoint = p: CodePoint | HIGH_SURROGATE_MIN <= p <= HIGH_SURROGATE_MAX
    witness HIGH_SURROGATE_MIN
  const HIGH_SURROGATE_MIN: CodePoint := 0xD800
  const HIGH_SURROGATE_MAX: CodePoint := 0xDBFF

  /**
   * A Unicode code point in the range U+DC00 to U+DFFF. (Section 3.8 D73)
   */
  type LowSurrogateCodePoint = p: CodePoint | LOW_SURROGATE_MIN <= p <= LOW_SURROGATE_MAX
    witness LOW_SURROGATE_MIN
  const LOW_SURROGATE_MIN: CodePoint := 0xDC00
  const LOW_SURROGATE_MAX: CodePoint := 0xDFFF

  /**
   * Any Unicode code point except high-surrogate and low-surrogate code points. (Section 3.9 D76)
   */
  type ScalarValue = p: CodePoint |
    && (p < HIGH_SURROGATE_MIN || p > HIGH_SURROGATE_MAX)
    && (p < LOW_SURROGATE_MIN || p > LOW_SURROGATE_MAX)

  type AssignedCodePoint = p: CodePoint | IsAssignedCodePoint(p) witness *

  predicate {:opaque} IsAssignedCodePoint(i: CodePoint) {
    var plane := (i >> 16) as bv8;
    if plane == 0 then IsInBasicMultilingualPlane(i)
    else if plane == 1 then IsInSupplementaryMultilingualPlane(i)
    else if plane == 2 then IsInSupplementaryIdeographicPlane(i)
    else if plane == 3 then IsInTertiaryIdeographicPlane(i)
    else if plane == 14 then IsInSupplementarySpecialPurposePlane(i)
    else if 15 <= plane <= 16 then IsInSupplementaryPrivateUseAreaPlanes(i)
    else (
      assert 4 <= plane <= 13;  // planes 4-13 are unassigned
      false
    )
  }

  // These are actually supersets of the Unicode planes,
  // since not all code points in a plane are assigned.
  //
  // TODO: correctly check code points against the list of assigned code points
  // (https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt)

  predicate IsInBasicMultilingualPlane(i: CodePoint)
    requires 0x0000 <= i <= 0xFFFF  // BMP is plane 0
  {
    || 0x0000 <= i <= 0x007F  // Basic Latin
    || 0x0080 <= i <= 0x00FF  // Latin-1 Supplement
    || 0x0100 <= i <= 0x017F  // Latin Extended-A
    || 0x0180 <= i <= 0x024F  // Latin Extended-B
    // TODO add the rest of the 164 blocks
  }

  predicate IsInSupplementaryMultilingualPlane(i: CodePoint)
    requires 0x10000 <= i <= 0x1FFFF  // SMP is plane 1
  {
    && true  // TODO add the 145 SMP blocks
  }

  predicate IsInSupplementaryIdeographicPlane(i: CodePoint)
    requires 0x20000 <= i <= 0x2FFFF  // SIP is plane 2
  {
    || 0x20000 <= i <= 0x2A6DF  // CJK Unified Ideographs Extension B
    || 0x2A700 <= i <= 0x2B73F  // CJK Unified Ideographs Extension C
    || 0x2B740 <= i <= 0x2B81F  // CJK Unified Ideographs Extension D
    || 0x2B820 <= i <= 0x2CEAF  // CJK Unified Ideographs Extension E
    || 0x2CEB0 <= i <= 0x2EBEF  // CJK Unified Ideographs Extension F
    || 0x2F800 <= i <= 0x2FA1F  // CJK Compatibility Ideographs Supplement
  }

  predicate IsInTertiaryIdeographicPlane(i: CodePoint)
    requires 0x30000 <= i <= 0x3FFFF  // TIP is plane 3
  {
    || 0x30000 <= i <= 0x3134F  // CJK Unified Ideographs Extension G
  }

  predicate IsInSupplementarySpecialPurposePlane(i: CodePoint)
    requires 0xE0000 <= i <= 0xEFFFF  // SSP is plane 14
  {
    || 0xE0000 <= i <= 0xE007F  // Tags
    || 0xE0100 <= i <= 0xE01EF  // Variation Selectors Supplement
  }

  predicate IsInSupplementaryPrivateUseAreaPlanes(i: CodePoint)
    requires
      || 0xF0000 <= i <= 0xFFFFF  // SPUA-A is plane 15
      || 0x100000 <= i <= 0x10FFFF  // SPUA-B is plane 16
  {
    || 0xF0000 <= i <= 0xFFFFD  // Supplementary Private Use Area-A
    || 0x100000 <= i <= 0x10FFFD  // Supplementary Private Use Area-B
  }
}
