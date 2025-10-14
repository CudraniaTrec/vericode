
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[a.Length - 1 - j]) && a[a.Length - 1 - j] == old(a[j])
    invariant forall j :: i <= j < a.Length - i ==> a[j] == old(a[j])
    decreases a.Length / 2 - i
  {
    a[i], a[a.Length-1-i] := a[a.Length-1-i], a[i];
    i := i + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
