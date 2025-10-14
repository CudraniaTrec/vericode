
// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that function applications yield trigger candidates

method M(P: (int -> int) -> bool, g: int -> int)
  requires P.requires(g)
  requires P(g) {
  assume forall f: int -> int :: P.requires(f);
  assume forall f: int -> int :: P(f) ==> f.requires(10) && f(10) == 0;
  // strongest possible assertions and invariants
  assert forall f: int -> int :: P(f) ==> f.requires(10);
  assert forall f: int -> int :: P(f) ==> f(10) == 0;
  assert P(g);
  assert g.requires(10);
  assert g(10) == 0;
  // The main implication
  assert (forall f: int -> int, x: int :: f.requires(x) && g.requires(x) && (forall y :: f.requires(y) && g.requires(y) ==> f(y) == g(y)) ==> f(x) == g(x));
  // The implication in the code
  assert forall f: int -> int ::
    ((forall x :: f.requires(x) && g.requires(x) ==> f(x) == g(x)) ==>
    (f.requires(10) ==> f(10) == 0));
  (forall x :: f.requires(x) && g.requires(x) ==> f(x) == g(x)) ==>
    f.requires(10) ==>
    f(10) == 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
