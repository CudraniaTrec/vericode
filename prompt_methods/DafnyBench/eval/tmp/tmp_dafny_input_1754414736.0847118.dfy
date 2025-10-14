method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
{
  var i := 0;
  max := 0;

  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant 0 <= max < a.Length;
    invariant forall x :: 0 <= x < i ==> a[max] >= a[x];
  {
    if (a[i] > a[max]) { max := i; }
    i := i + 1;
  }
  return max;
}

function abs(a: real) : real {if a>0.0 then a else -a}
