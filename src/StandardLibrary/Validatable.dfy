module ExternalInvariants {

  trait {:termination false} Validatable {
    ghost const Repr: set<Validatable>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    predicate P() {
      true
    }

    twostate lemma AllStillValid() 
      requires old(AllValid(set v: Validatable | allocated(v) && v.P()))
      requires Valid()
      requires forall o :: o !in Repr ==> unchanged(o)
      requires forall o :: o in Repr ==> o.Valid()
      ensures AllValid(set v: Validatable | allocated(v) && v.P())
    {
      forall v: Validatable | old(allocated(v)) && v.P() ensures v.Valid() {
        IndependentValidityInductive(v, Repr);
      }
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
  }

  // This is the "external invariant". It must hold as a precondition and postcondition for
  // every method that crosses the Dafny/external boundary, either incoming or outgoing.
  // It assumes that the Dafny heap cannot be changed in any other way.
  // I have to pass in the set of objects implementing Validatable since I can't pass in
  // "the Dafny heap".
  predicate AllValid(vs: set<Validatable>) 
    reads vs
    reads set v, o | v in vs && o in v.Repr :: o
  {
    forall v :: v in vs ==> v.Valid()
  }

  twostate lemma IndependentValidityInductive(v: Validatable, changed: set<Validatable>)
      requires old(AllValid(set v': Validatable | allocated(v') && v'.P()))
      requires forall o :: o !in changed ==> unchanged(o)
      requires forall o :: o in changed ==> o.Valid()
      requires allocated(v)
      decreases v.Repr
      ensures v.Valid()
  {
    assert old(v.Valid());
    forall v': Validatable | v' in v.Repr && v' != v && old(allocated(v')) ensures v'.Valid() {
      IndependentValidityInductive(v', changed);
    }
    if v !in changed {
      v.IndependentValidity();
    }
  }
}