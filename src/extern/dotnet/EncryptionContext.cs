using System;
using System.Linq;
using System.Collections.Generic;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;

namespace EncryptionContext {

  public partial class __default {

    public static Dafny.Map<ibyteseq,ibyteseq> LinearToMap(Dafny.ISequence<_System.Tuple2<ibyteseq,ibyteseq>> kvPairs) {
        Dictionary<ibyteseq, ibyteseq> dict = kvPairs.Elements.ToDictionary(
            item => item._0,
            item => item._1);
        List<Dafny.Pair<ibyteseq, ibyteseq>> pairs = new List<Dafny.Pair<ibyteseq, ibyteseq>>();

        foreach(KeyValuePair<ibyteseq, ibyteseq> entry in dict) {
            pairs.Add(new Dafny.Pair<ibyteseq, ibyteseq>(entry.Key, entry.Value));
        }
        return Dafny.Map<ibyteseq,ibyteseq>.FromCollection(pairs);
    }
  }
}
