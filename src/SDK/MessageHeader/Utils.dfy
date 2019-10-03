include "../AlgorithmSuite.dfy"
include "../../Util/Streams.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"
include "../../Util/UTF8.dfy"

module MessageHeader.Utils {
  import AlgorithmSuite
  import Streams
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt

  predicate SortedKVPairsUpTo(a: seq<(seq<uint8>, seq<uint8>)>, n: nat)
    requires n <= |a|
  {
    forall j :: 0 < j < n ==> LexicographicLessOrEqual(a[j-1].0, a[j].0, UInt8Less)
  }

  predicate SortedKVPairs(a: seq<(seq<uint8>, seq<uint8>)>)
  {
    SortedKVPairsUpTo(a, |a|)
  }

  method InsertNewEntry(kvPairs: seq<(seq<uint8>, seq<uint8>)>, key: seq<uint8>, value: seq<uint8>)
      returns (res: Option<seq<(seq<uint8>, seq<uint8>)>>, ghost insertionPoint: nat)
    requires SortedKVPairs(kvPairs)
    ensures match res
    case None =>
      exists i :: 0 <= i < |kvPairs| && kvPairs[i].0 == key  // key already exists
    case Some(kvPairs') =>
      && insertionPoint <= |kvPairs|
      && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]
      && SortedKVPairs(kvPairs')
  {
    var n := |kvPairs|;
    while 0 < n && LexicographicLessOrEqual(key, kvPairs[n - 1].0, UInt8Less)
      invariant 0 <= n <= |kvPairs|
      invariant forall i :: n <= i < |kvPairs| ==> LexicographicLessOrEqual(key, kvPairs[i].0, UInt8Less)
    {
      n := n - 1;
    }
    if 0 < n && kvPairs[n - 1].0 == key {
      return None, n;
    } else {
      var kvPairs' := kvPairs[..n] + [(key, value)] + kvPairs[n..];
      if 0 < n {
        LexPreservesTrichotomy(kvPairs'[n - 1].0, kvPairs'[n].0, UInt8Less);
      }
      return Some(kvPairs'), n;
    }
  }
}
