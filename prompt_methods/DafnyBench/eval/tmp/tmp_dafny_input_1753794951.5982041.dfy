predicate sorted (a: array<int>)
  reads a
{
  sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)
  requires 0 <= i <= a.Length
  reads a
{
  forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

method lookForMin (a: array<int>, i: int) returns (m: int)
  requires 0 <= i < a.Length
  ensures i <= m < a.Length
  ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  var j := i;
  m := i;
  while(j < a.Length)
    invariant i <= j <= a.Length
    invariant i <= m < a.Length
    invariant forall k :: i <= k < j ==> a[k] >= a[m]
  {
    if(a[j] < a[m]) { m := j; }
    j := j + 1;
  }
  assert i <= m < a.Length;
  assert forall k :: i <= k < a.Length ==> a[k] >= a[m];
}

method insertionSort (a: array<int>)
  modifies a
  ensures sorted(a)
{
  var c := 0;
  while(c < a.Length)
    invariant 0 <= c <= a.Length
    invariant sortedA(a, c)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var m := lookForMin(a, c);
    a[m], a[c] := a[c], a[m];
    // After swapping, a[c] is the minimum of a[c..a.Length)
    // sortedA(a, c+1) holds because a[c] is <= all a[c+1..a.Length)
    // and sortedA(a, c) held before
    c := c + 1;
  }
  assert sorted(a);
}
function abs(a: real) : real {if a>0.0 then a else -a}
