include "../StandardLibrary/StandardLibrary.dfy"
include "../StandardLibrary/Orders.dfy"

module {:extern "Sets"} Sets {
  import opened StandardLibrary

  method {:extern "SetToOrderedSequence"} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Orders.Trichotomous(less) && Orders.Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
}
