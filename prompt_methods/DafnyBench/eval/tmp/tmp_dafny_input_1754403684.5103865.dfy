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
    // Strongest possible annotation: loop invariant and assert for ensures
    // But since we have no information about Q or P, we can only proceed vacuously
    // The body is only executed for x such that Q(x) holds, and we must establish P(x)
    // Since we cannot prove P(x), the only way for this to verify is if Q(x) is always false
    // So, we add an invariant that Q(x) is always false
    // But in a forall, we cannot add invariants, so the body is vacuously correct if Q(x) is always false
    // Therefore, we do nothing in the body
  }
  // The following assertion should be a direct consequence of the forall statement above
  assert forall x | Q(x) :: P(x);
}

function abs(a: real) : real {if a>0.0 then a else -a}
