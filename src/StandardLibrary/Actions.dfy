// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"

module Actions {

  import opened Wrappers

  trait {:termination false} Action<A, R>
  {
    method Invoke(a: A)
      returns (r: R)
      ensures Ensures(a, r)
    predicate Ensures(a: A, r: R)
  }

  trait {:termination false} ActionWithResult<A, R, E>
    extends Action<A, Result<R, E>>
  {
    method Invoke(a: A)
      returns (res: Result<R, E>)
      ensures Ensures(a, res)
  }

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
