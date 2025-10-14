method HasCommonElement(a: array<int>, b: array<int>) returns (res: bool)
{
  res := false;
  var i := 0;
  while i < a.Length && !res
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> forall l :: 0 <= l < b.Length ==> a[k] != b[l]
    invariant !res ==> forall k :: 0 <= k < i ==> forall l :: 0 <= l < b.Length ==> a[k] != b[l]
  {
    var j := 0;
    while j < b.Length && !res
      invariant 0 <= j <= b.Length
      invariant forall l :: 0 <= l < j ==> a[i] != b[l]
      invariant !res ==> forall l :: 0 <= l < j ==> a[i] != b[l]
    {
      if a[i] == b[j] {
        res := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}