method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
  p := 0;
  var best := a[0];
  var i := 1;
  while i < x
    invariant 1 <= x < a.Length
    invariant 0 <= i <= x
    invariant 0 <= p < a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= best
    invariant exists j :: 0 <= j < i && a[j] == best
    invariant best == (if i == 0 then a[0] else (if i > 0 then (max k | 0 <= k < i :: a[k]) else a[0]))
  {
    if a[i] > best {
      best := a[i];
    }
    i := i + 1;
  }
  m := best;
  i := x;
  while i < a.Length
    invariant x <= i <= a.Length
    invariant m == best
    invariant forall j :: 0 <= j < x ==> a[j] <= m
    invariant exists j :: 0 <= j < x && a[j] == m
    invariant forall j :: x <= j < i ==> a[j] <= m
    invariant p == 0
  {
    if a[i] > best {
      p := i;
      assert forall j :: 0 <= j < x ==> a[j] < a[p];
      return;
    }
    i := i + 1;
  }
  p := a.Length - 1;
  assert forall j :: x <= j < a.Length ==> a[j] <= m;
}

function abs(a: real) : real {if a>0.0 then a else -a}
