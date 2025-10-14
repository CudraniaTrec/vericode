method UpdateElements(a: array<int>)
  requires a.Length >= 8
  modifies a
  ensures old(a[4]) +3 == a[4]
  ensures a[7]==516
  ensures forall i::0 <= i<a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i])
{
  // At this point: forall i:: 0 <= i < a.Length ==> a[i] == old(a[i])
  assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]);
  a[4] := a[4] + 3;
  // After this: a[4] == old(a[4]) + 3, and for all i != 4, a[i] == old(a[i])
  assert a[4] == old(a[4]) + 3;
  assert forall i :: 0 <= i < a.Length && i != 4 ==> a[i] == old(a[i]);
  a[7] := 516;
  // After this: a[7] == 516, a[4] == old(a[4]) + 3, and for all i != 4,7, a[i] == old(a[i])
  assert a[7] == 516;
  assert a[4] == old(a[4]) + 3;
  assert forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> a[i] == old(a[i]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
