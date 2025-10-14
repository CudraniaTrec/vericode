predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

method selSort (a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
  if (c <= f-1) { // two elements at least
    var i := c;
    while (i < f-1)
      invariant c <= i <= f
      invariant sorted_seg(a, c, i)
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k < i ==> forall m :: i <= m < f ==> a[k] <= a[m]
    {
      var less := i;
      var j := i+1;
      while (j < f)
        invariant i+1 <= j <= f
        invariant i <= less < f
        invariant forall k :: i <= k < j ==> a[less] <= a[k]
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      {
        if (a[j] < a[less]) {
          less := j;
        }
        j := j + 1;
      }
      // Swap a[i] and a[less]
      var tmp := a[i];
      a[i] := a[less];
      a[less] := tmp;
      i := i + 1;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
