include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/Collections.dfy"

module TestIO {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened Collections

  method {:test} IntSeqEnumerator() {
    var testSeq := [1, 2, 3];
    var seqEnum := new SeqEnumerator<int>(testSeq);
      
    var res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == 1;
    res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == 2;
    res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == 3;
    res := seqEnum.Next();
    expect res.Success? && res.value == None();
    res := seqEnum.Next();
    expect res.Failure?;
  }

  method {:test} IntSeqAggregator() {
    var seqAgg := new SeqAggregator<int>();

    var res2 := seqAgg.Accept(1);
    expect res2.Success? && res2.value && seqAgg.s == [1];
    res2 := seqAgg.Accept(2);
    expect res2.Success? && res2.value && seqAgg.s == [1, 2];
    res2 := seqAgg.End();
    expect res2.Success? && res2.value;
    res2 := seqAgg.Accept(1);
    expect res2.Failure?;
    res2 := seqAgg.End();
    expect res2.Failure?;
  }
  
  method {:test} IntSeqChunkEnumerator() {
    var testSeq := [1, 2, 3, 4, 5];
    var seqEnum := new SeqChunkEnumerator<int>(testSeq, 2);
      
    var res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == [1, 2];
    res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == [3, 4];
    res := seqEnum.Next();
    expect res.Success? && res.value.Some? && res.value.get == [5];
    res := seqEnum.Next();
    expect res.Success? && res.value == None();
    res := seqEnum.Next();
    expect res.Failure?;
  }

  method {:test} IntSeqChunkAggregator() {
    var seqAgg := new SeqChunkAggregator<int>();

    var res2 := seqAgg.Accept([1,2,3]);
    expect res2.Success? && res2.value && seqAgg.s == [1,2,3];
    res2 := seqAgg.Accept([4,5]);
    expect res2.Success? && res2.value && seqAgg.s == [1,2,3,4,5];
    res2 := seqAgg.End();
    expect res2.Success? && res2.value;
    res2 := seqAgg.Accept([1]);
    expect res2.Failure?;
    res2 := seqAgg.End();
    expect res2.Failure?;
  }
}
