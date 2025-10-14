method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i :: 0 <= i < n ==> forall k :: n <= k < a.Length ==> a[i] <= a[k]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
      invariant n <= mindex < m || m == n
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
      assert multiset(a[..]) == old(multiset(a[..]));
    }
    n := n + 1;
  }  
}

function abs(a: real) : real {if a>0.0 then a else -a}
