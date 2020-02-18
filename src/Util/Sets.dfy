include "../StandardLibrary/StandardLibrary.dfy"

module {:extern "Sets"} Sets {
  import opened StandardLibrary

  method {:extern "SetToOrderedSequence"} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
}
