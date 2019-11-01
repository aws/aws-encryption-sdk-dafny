// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/Folding.dfy"

module TestFolding {

  import opened Folding
  
  method Main() {

    var xs := [57, 100, -34, 1, 8];
    var r := foldr((a,b) => 2*a + b, 0, xs);
    var l := foldl((b,a) => b + 2*a, 0, xs);
    print "xs = ", xs, "\n";
    print "foldr = ", r, "\n";
    print "foldl = ", l, "\n";
    print "length = ", |xs|, "\n";
    print "foldr inc = ", foldr((_,b) => b+1, 0, xs), "\n";
    print "foldl inc = ", foldl((b,_) => b + 1, 0, xs), "\n";
  }

  // ----- foldr ----------

  method FoldR_Use(xs: seq<int>)
  {
    var f := (a,b) => 2*a + 3*b;
    var r := foldr(f, 0, xs);
    ghost var inv := (xs,b) => b % 2 == 0;
    ghost var stp := (a,b,b') => b % 2 == 0 ==> b' % 2 == 0;
    FoldR_Property(inv, stp, f, 0, xs);
    assert r % 2 == 0;
  }

  // The (inv,stp) method of proof above is general, in the sense that it can be instantiated with (inv,stp).
  // For a particular function, like F23, one can also prove a lemma about foldr directly.
  function method F23(a: int, b: int): int {
    2*a + 3*b
  }

  lemma FoldR_F23(xs: seq<int>)
    ensures foldr(F23, 0, xs) % 2 == 0
  {
    // Dafny proves this lemma automatically
  }

  // In fact, it's also possible to write this lemma in an inline assertion.
  method FoldR_Use_Direct(xs: seq<int>)
  {
    var r := foldr(F23, 0, xs);
    assert forall ys :: foldr(F23, 0, ys) % 2 == 0;
    assert r % 2 == 0;
  }

  method FoldR_Use_Direct_lambda(xs: seq<int>)
  {
    var f := (a,b) => 2*a + 3*b;
    var r := foldr(f, 0, xs);
    assert forall ys :: foldr(f, 0, ys) % 2 == 0;
    assert r % 2 == 0;
  }

  // ----- foldl ----------

  lemma FoldL_Use(xs: seq<int>)
  {
    var f := (b,a) => 3*b + 2*a;
    var l := foldl(f, 0, xs);
    ghost var inv := (b,xs) => b % 2 == 0;
    ghost var stp := (b,a,b') => b % 2 == 0 ==> b' % 2 == 0;
    FoldL_Property(inv, stp, f, 0, xs);
    assert l % 2 == 0;
  }

  // And as in the case of foldr, one can also use a specialized lemma for a particular function to be folded.
  function method F32(b: int, a: int): int
  {
    3*b + 2*a
  }

  lemma FoldL_F32(xs: seq<int>, b: int)
    requires b % 2 == 0
    ensures foldl(F32, b, xs) % 2 == 0
  {
  }

  method FoldL_Use_Direct(xs: seq<int>)
  {
    var r := foldl(F32, 0, xs);
    assert forall ys,b :: b % 2 == 0 ==> foldl(F32, b, ys) % 2 == 0;
    assert r % 2 == 0;
  }

  method FoldL_Use_Direct_lambda(xs: seq<int>)
  {
    var f := (b,a) => 3*b + 2*a;
    var r := foldl(f, 0, xs);
    assert forall ys,b :: b % 2 == 0 ==> foldl(f, b, ys) % 2 == 0;
    assert r % 2 == 0;
  }
}