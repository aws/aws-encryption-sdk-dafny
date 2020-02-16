using System;
using System.Linq;
using System.Collections.Generic;
using byteseq = Dafny.Sequence<byte>;

namespace MessageHeader {

  public partial class __default {

    public static Dafny.Map<byteseq,byteseq> KVPairSequenceToMap(Dafny.Sequence<_System.Tuple2<byteseq,byteseq>> kvPairs) {
        Dictionary<byteseq, byteseq> dict = kvPairs.Elements.ToDictionary(
            item => item._0,
            item => item._1);
        List<Dafny.Pair<byteseq, byteseq>> pairs = new List<Dafny.Pair<byteseq, byteseq>>();

        foreach(KeyValuePair<byteseq, byteseq> entry in dict)
        {
            pairs.Add(new Dafny.Pair<byteseq, byteseq>(entry.Key, entry.Value));
        }
        return Dafny.Map<byteseq,byteseq>.FromCollection(pairs);
    }
  }
}
