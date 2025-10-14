predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i:nat := 1;

  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i <= a.Length
      invariant sorted(a, 0, j)
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: j < k <= i ==> a[k-1] <= a[k]
    {
      assert 1 <= j <= a.Length;
      if (a[j-1] > a[j]) {
        var temp:int := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
