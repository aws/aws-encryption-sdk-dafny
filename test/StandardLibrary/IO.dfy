include "../../src/StandardLibrary/UInt.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/IO.dfy"

module TestIO {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import opened IO

  method {:test} BytesSeqEnumerator() {
    var testSeq := [1, 2, 3, 4, 5];
    var seqEnum := new BytesSeqEnumerator(testSeq, 2);
      
    var res := seqEnum.Next(); // TODO: call may violate context's modifies clause
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
}
