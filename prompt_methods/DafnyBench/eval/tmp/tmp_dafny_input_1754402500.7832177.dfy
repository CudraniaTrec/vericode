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
  if (c<=f-1){//two elements at least
    var i := c;
    while (i < f-1) //outer loop
      invariant c <= i <= f
      invariant a[..c] == old(a[..c])
      invariant a[f..] == old(a[f..])
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant sorted_seg(a, c, i)
      invariant forall k :: c <= k < i ==> forall l :: k < f ==> a[k] <= a[l]
    {
      var less := i;
      var j := i+1;
      while (j < f) //inner loop
        invariant i+1 <= j <= f
        invariant c <= less < f
        invariant i <= less < f
        invariant forall k :: i+1 <= k < j ==> a[less] <= a[k]
        invariant less == (forall k :: i+1 <= k < j :: a[less] <= a[k]) && (exists k :: i+1 <= k < j && a[less] == a[k]) || (j == i+1 && less == i)
      {
        if (a[j] < a[less]) { less := j; }
        j := j+1;
      }
      // After inner loop: less is the index of the minimal element in a[i..f)
      a[i], a[less] := a[less], a[i];
      i := i+1;
    }
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
