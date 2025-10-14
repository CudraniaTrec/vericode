
method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{
  var j : int := 0;
  while(j < a.Length)
    invariant 0 <= j <= a.Length
    invariant forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1
    invariant forall i :: j <= i < a.Length ==> a[i] == old(a[i])
  {
    a[j] := a[j] + 1;
    j := j+1;   
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
