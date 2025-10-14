method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var i := a.Length - 1;
  while (i > 0)
    invariant 0 <= i < a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: i < k < a.Length ==> a[k-1] <= a[k]
    invariant forall k :: i < k < a.Length ==> forall l :: 0 <= l < i ==> a[l] <= a[k]
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j <= i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: i < k < a.Length ==> a[k-1] <= a[k]
      invariant forall k :: i < k < a.Length ==> forall l :: 0 <= l < i ==> a[l] <= a[k]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[k+1]
    {
      if (a[j] > a[j + 1])
      {
        a[j], a[j + 1] := a[j + 1], a[j];
        assert multiset(a[..]) == multiset(old(a[..]));
      }
      j := j + 1;
    }
    i := i - 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
