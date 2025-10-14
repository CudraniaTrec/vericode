method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
{
  // assert 0 <= j < a.Length; // implied by precondition
  var oldA := a[..];
  a[j] := 60;
  assert a[j] == 60;
  assert forall k :: 0 <= k < a.Length && k != j ==> a[k] == oldA[k];
}
function abs(a: real) : real {if a>0.0 then a else -a}
