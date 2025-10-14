predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

method bubbleSorta(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
  var i := c;
  while (i < f)
    invariant c <= i <= f
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant forall k :: c <= k < i ==> forall l :: k < f ==> a[k] <= a[l]
  {
    var j := f - 1;
    while (j > i)
      invariant c <= i < f
      invariant i < j <= f
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k < i ==> forall l :: k < f ==> a[k] <= a[l]
      invariant forall k :: j < k < f ==> a[j-1] <= a[k]
    {
      if (a[j-1] > a[j]) {
        a[j], a[j-1] := a[j-1], a[j];
      }
      j := j - 1;
    }
    i := i + 1;
  }
}

method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
  var i := c;
  var b := true;
  while (i < f && b)
    invariant c <= i <= f
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant forall k :: c <= k < i ==> forall l :: k < f ==> a[k] <= a[l]
    invariant b ==> exists k :: i <= k < f-1 :: a[k] > a[k+1]
  {
    var j := f - 1;
    b := false;
    while (j > i)
      invariant c <= i < f
      invariant i < j <= f
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k < i ==> forall l :: k < f ==> a[k] <= a[l]
      invariant forall k :: j < k < f ==> a[j-1] <= a[k]
    {
      if (a[j-1] > a[j]) {
        a[j], a[j-1] := a[j-1], a[j];
        b := true;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
