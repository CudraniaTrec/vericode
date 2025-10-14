// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node { }

predicate Q(x: Node)
predicate P(x: Node)

method AuxMethod(y: Node)
  modifies y

method MainMethod(y: Node)
  modifies y
{
  AuxMethod(y);  // remove this call and the assertion below goes through (as it should)

  forall x | Q(x)
    ensures P(x)
  {
    // Strongest possible annotation: Q(x) ==> P(x) must be established for all x
    // But with no further information, we cannot prove P(x) for arbitrary x: so we leave the body empty.
    // No loop, so no invariants.
  }
  // The following assertion should be a direct consequence of the forall statement above
  assert forall x | Q(x) :: P(x);
}

function abs(a: real) : real {if a>0.0 then a else -a}
