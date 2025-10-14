
method LinearSearch(a: array<int>, e: int) returns (n:int)
  requires exists i::0<=i<a.Length && a[i]==e
  ensures 0<=n<a.Length && a[n]==e
  ensures forall k :: 0 <= k < n ==> a[k]!=e

{
  n :=0;
  while n!=a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> a[k] != e
    invariant exists i :: n <= i < a.Length && a[i] == e
  {
    if e==a[n]{
      assert 0 <= n < a.Length;
      assert a[n] == e;
      return;
    }
    n:=n+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
