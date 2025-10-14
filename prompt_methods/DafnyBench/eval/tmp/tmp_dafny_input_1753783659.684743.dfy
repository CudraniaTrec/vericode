
method UpdateElements(a: array<int>)
  requires a.Length >= 8
  modifies a
  ensures old(a[4]) +3 == a[4]
  ensures a[7]==516
  ensures forall i::0 <= i<a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i])
{
  // assert a.Length >= 8; // implied by precondition
  var old4 := a[4];
  var old7 := a[7];
  // assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]);
  a[4] := a[4] + 3;
  // assert a[4] == old4 + 3;
  a[7] := 516;
  // assert a[7] == 516;
  // assert forall i :: 0 <= i < a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
