include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/Util/UTF8.dfy"

module {:extern "TestUtils"} TestUtils {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import UTF8

  const SHARED_TEST_KEY_ARN := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f";

  // TODO correctly verify UTF8 validity of long sequences
  // This axiom should only be used by tests to skip UTF8 verification of long sequences
  // long to be serialized in 16 bytes, in order to avoid a false negative for from verification.
  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 0x1_0000
    ensures UTF8.ValidUTF8Seq(s)
}
