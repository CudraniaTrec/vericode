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
    // strongest possible annotation: if Q(x) holds, must establish P(x)
    if Q(x) {
      // Here, we would need to show P(x), but we have no information, so:
      assert false;
    }
  }
  // The following assertion should be a direct consequence of the forall statement above
  assert forall x | Q(x) :: P(x);
}

function abs(a: real) : real {if a>0.0 then a else -a}
