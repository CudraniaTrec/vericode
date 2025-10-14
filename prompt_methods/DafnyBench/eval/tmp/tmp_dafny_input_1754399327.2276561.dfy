
method LinearSearch(a: array<int>, e: int) returns (n:int)
  ensures 0<=n<=a.Length
  ensures n==a.Length || a[n]==e
  ensures forall i::0<=i < n ==> e!=a[i]
{
  n :=0;
  while n!=a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] != e
    invariant n <= a.Length
    decreases a.Length - n
  {
    if e==a[n]{
      assert a[n] == e;
      assert forall i :: 0 <= i < n ==> a[i] != e;
      return;
    }
    n:=n+1;
  }
  assert n == a.Length;
  assert forall i :: 0 <= i < n ==> a[i] != e;
}

function abs(a: real) : real {if a>0.0 then a else -a}
