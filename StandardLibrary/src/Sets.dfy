// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"

module {:extern "Sets"} Sets {
  import opened StandardLibrary
  import Seq

  method {:extern "SetToOrderedSequence"} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)

  function method {:extern "SetToOrderedSequence2"} ComputeSetToOrderedSequence2<T(==)>(
    s: set<seq<T>>,
    less: (T, T) -> bool
  )
    :(res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    // The seq came from the set
    ensures Seq.HasNoDuplicates(res)
}
