method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
{
  // Strongest possible annotation: assert that all elements except j are unchanged
  assert forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k]);
  a[j] := 60;
  // Strongest possible annotation: assert that a[j] == 60
  assert a[j] == 60;
  // Strongest possible annotation: assert that all other elements are unchanged
  assert forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
