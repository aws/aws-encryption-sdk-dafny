// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"
include "../../libraries/src/Collections/Sequences/Seq.dfy"

module Actions {

  import opened Wrappers
  import opened Seq

  datatype ActionInvoke<A, R> = ActionInvoke(input: A, output: R)
  /*
   * A trait that can execute arbitrary actions on input type A
   * and return results of type R.
   */
  trait {:termination false} Action<A, R>
  {
    /*
     * Contains the implementation of the given action
     */
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, R>>)
      returns (r: R)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)

    predicate Invariant()
      reads Modifies
      decreases Modifies

    /*
     * Contains the assertions that should be true upon return of the Invoke method
     */
    predicate Ensures(
      a: A,
      r: R,
      attemptsState: seq<ActionInvoke<A, R>>
    )
      reads Modifies
      decreases Modifies

    /*
     * Contains the set of fields that may be modified during `Invoke`
     */
    ghost const Modifies: set<object>
  }

  /*
   * A trait that can execute actions which can fail. Is invoked on inputs
   * of type A, and returns Result types which contain type R on success
   * or type E on failure.
   */
  trait {:termination false} ActionWithResult<A, R, E>
    extends Action<A, Result<R, E>>
  {
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, Result<R, E>>>)
      returns (r: Result<R, E>)
      requires Invariant()
      modifies Modifies
      decreases Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)
  }

    trait {:termination false} DeterministicAction<A, R>
  {
    /*
     * Contains the implementation of the given deterministic action
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
   * A trait that can execute deterministic actions which can fail.
   * Is invoked on inputs of type A,
   * and returns Result types which contain type R on success
   * or type E on failure.
   */
  trait {:termination false} DeterministicActionWithResult<A, R, E>
    extends DeterministicAction<A, Result<R, E>>
  {
    method Invoke(a: A)
      returns (r: Result<R, E>)
      ensures Ensures(a, r)
  }

/*
   * Returns a sequence with elements of type R
   * which is built by executing the input action
   * to all items in the input sequence.
   *
   * This operation MUST be deterministic.
   */
  method DeterministicMap<A, R>(
    action: DeterministicAction<A, R>,
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
  method DeterministicMapWithResult<A, R, E>(
    action: DeterministicActionWithResult<A, R, E>,
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
   * A specialized version of the Map method whose action always returns sequences, which
   * are flattened into a single final result. This flattening only happens once, rather
   * than recursively; that is, if the action returns a sequence of sequences, the return
   * of this method will also be a sequence of sequences.
   */
  method DeterministicFlatMap<A, R>(
    action: DeterministicAction<A, seq<R>>,
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
   *
   * Also returns a ghost variable containing the unflattened version of
   * the action's return sequences, which may be useful in helping callers
   * prove things.
   */
  method DeterministicFlatMapWithResult<A, R, E>(
    action: DeterministicActionWithResult<A, seq<R>, E>,
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
    action: DeterministicAction<A, bool>,
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
    action: DeterministicActionWithResult<A, bool, E>,
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
   * the successful attempt's result. If all fail, this method returns a single
   * failure which aggregates all failures.
   */
    method ReduceToSuccess<A, B, E>(
    action: ActionWithResult<A, B, E>,
    s: seq<A>
  )
    returns (
      res: Result<B, seq<E>>,
      ghost attemptsState: seq<ActionInvoke<A, Result<B, E>>>
    )
    requires 0 < |s|
    requires action.Invariant()
    modifies action.Modifies
    decreases action.Modifies
    ensures 0 < |attemptsState| <= |s|
    ensures forall i
      | 0 <= i < |attemptsState|
      :: attemptsState[i].input == s[i]
    ensures action.Invariant() // this feels a little strange
    ensures
    if res.Success? then
      && Last(attemptsState).output.Success?
      && Last(attemptsState).output.value == res.value
      // This is the engine that can be used to hoist proof obligations
      && action.Ensures(
        Last(attemptsState).input,
        Last(attemptsState).output,
        DropLast(attemptsState))
      // Attempts are made until there is a success
      // so attemps will be amde up of failures
      // with one final Success at the end.
      && forall i
      | 0 <= i < |DropLast(attemptsState)|
      :: attemptsState[i].output.Failure?
    else
      && |attemptsState| == |s|
      && forall i
      | 0 <= i < |attemptsState|
      :: attemptsState[i].output.Failure?
  {
    var attemptedResults := [];
    attemptsState := [];
    for i := 0 to |s|
      invariant |s[..i]| == |attemptsState| == |attemptedResults|
      invariant forall j
      | 0 <= j < |attemptsState|
      ::
        && attemptsState[j].input == s[j]
        && attemptsState[j].output.Failure?
        && attemptedResults[j] == attemptsState[j].output
      invariant action.Invariant()
    {
      var attempt := action.Invoke(s[i], attemptsState);

      attemptsState := attemptsState + [ActionInvoke(s[i], attempt)];
      attemptedResults := attemptedResults + [attempt];

      if attempt.Success? {
        return Success(attempt.value), attemptsState;
      }
    }
    res := Failure(Seq.Map(pluckErrors, attemptedResults));
  }

  function method pluckErrors<B, E>(r: Result<B, E>)
    :(e: E)
    requires r.Failure?
    ensures r.error == e
  {
    r.error
  }
}
