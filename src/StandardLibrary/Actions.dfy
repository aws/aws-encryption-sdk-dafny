// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"

module Actions {

  import opened Wrappers
  import opened Seq

  /*
   * A trait that can execute arbitrary actions on input type A
   * and return results of type R.
   */
  trait {:termination false} Action<A, R>
  {
    /*
     * Contains the implementation of the given action
     */
    method Invoke(a: A)
      returns (r: R)
      ensures Ensures(a, r)

    /*
     * Contains the assertions that should be true upon return of the Invoke method
     */
    predicate Ensures(a: A, r: R)
  }

  /*
   * A trait that can execute actions which can fail. Is invoked on inputs
   * of type A, and returns Result types which contain type R on success
   * or type E on failure.
   */
  trait {:termination false} ActionWithResult<A, R, E>
    extends Action<A, Result<R, E>>
  {
    method Invoke(a: A)
      returns (res: Result<R, E>)
      ensures Ensures(a, res)
  }

  /*
   * Returns a sequence with elements of type R which is built by executing the input action
   * to all items in the input sequence.
   */
  method Map<A, R>(
    action: Action<A, R>,
    s: seq<A>
  )
    returns (res: seq<R>)
    ensures |s| == |res|
    ensures
      forall i ::
        && 0 <= i < |s|
      ==>
        action.Ensures(s[i], res[i])
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j ::
        && 0 <= j < i
      ==>
        action.Ensures(s[j], rs[j])
    {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  /*
   * A specialized version of the Map method which allows actions that can fail.
   */
  // TODO: Change R(0) -> R once https://github.com/dafny-lang/dafny/issues/1553 resolved
  method MapWithResult<A, R(0), E>(
    action: ActionWithResult<A, R, E>,
    s: seq<A>
  )
    returns (res: Result<seq<R>, E>)
    ensures
      res.Success?
    ==>
      |s| == |res.value|
    ensures
      res.Success?
    ==>
        (forall i ::
          && 0 <= i < |s|
        ==>
          action.Ensures(s[i], Success(res.value[i])))
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j ::
        && 0 <= j < i
      ==>
        action.Ensures(s[j], Success(rs[j]))
    {
      var r :- action.Invoke(s[i]);
      rs := rs + [r];
    }
    return Success(rs);
  }

  /*
   * A specialized version of the Map method whose action always returns sequences.
   */
  method FlatMap<A, R>(
    action: Action<A, seq<R>>,
    s: seq<A>
  )
    returns (res: seq<R>)
    ensures
      forall i :: i in s
      ==>
        && exists fm :: action.Ensures(i, fm)
        && forall k | k in fm :: k in res
  {
    ghost var parts := [];
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j ::
        && 0 <= j < i
      ==>
        && action.Ensures(s[j], parts[j])
        && forall b | b in parts[j] :: b in rs
    {
      var r := action.Invoke(s[i]);
      rs := rs + r;
      parts := parts + [r];
    }
    return rs;
  }

  /*
   * A specialized version of the FlatMap method whose action may fail.
   */
  method FlatMapWithResult<A, R, E>(
    action: ActionWithResult<A, seq<R>, E>,
    s: seq<A>
  )
    returns (res: Result<seq<R>, E>, ghost parts: seq<seq<R>>)
    ensures
      res.Success?
    ==>
      && |s| == |parts|
      && res.value == Flatten(parts)
      && (forall i :: 0 <= i < |s|
      ==>
        && action.Ensures(s[i], Success(parts[i]))
        && multiset(parts[i]) <= multiset(res.value)
      )
  {
    parts := [];
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j ::
        && 0 <= j < i
      ==>
        && action.Ensures(s[j], Success(parts[j]))
        && multiset(parts[j]) <= multiset(rs)
      invariant Flatten(parts) == rs
    {
      var r :- action.Invoke(s[i]);
      rs := rs + r;
      LemmaFlattenConcat(parts, [r]);
      parts := parts + [r];
    }
    return Success(rs), parts;
  }

  /*
   * Given an input action (which must return a boolean) and an input sequence,
   * returns a sequence containing only those items from the input sequence which
   * return true when the action is invoked on them.
   */
  method Filter<A>(
    action: Action<A, bool>,
    s: seq<A>
  )
    returns (res: seq<A>)
    ensures |s| >= |res|
    ensures
      forall j ::
        j in res
      ==>
        && j in s
        && action.Ensures(j, true)
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j ::
        j in rs
      ==>
        && j in s
        && action.Ensures(j, true)
    {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }

  /*
   * Specialized version of Filter whose input action may fail.
   */
  method FilterWithResult<A, E>(
    action: ActionWithResult<A, bool, E>,
    s: seq<A>
  )
    returns (res: Result<seq<A>, E>)
    ensures
      res.Success?
    ==>
      && |s| >= |res.value|
      && forall j ::
        j in res.value
      ==>
        && j in s
        && action.Ensures(j, Success(true))
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j ::
        j in rs
      ==>
        && j in s
        && action.Ensures(j, Success(true))
    {
      var r :- action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  /*
   * Given an input action which may fail and an input sequence, executes the
   * given action on each element of the sequence until either one succeeds or
   * all have failed. If one succeeds, this method returns immediately with
   * the successful attempts result. If all fails, this method returns a single
   * failure which aggregates all failures.
   */
  method ReduceToSuccess<A, B, E>(
    action: ActionWithResult<A, B, E>,
    s: seq<A>
  )
    returns (res: Result<B, seq<E>>)
    ensures
      res.Success?
    ==>
      exists a | a in s :: action.Ensures(a, Success(res.value))
  {
    var errors := [];
    for i := 0 to |s| {
      var attempt := action.Invoke(s[i]);
      if attempt.Success? {
        return Success(attempt.value);
      } else {
        errors := errors + [attempt.error];
      }
    }
    return Failure(errors);
  }
}
