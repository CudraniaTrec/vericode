method IsSorted(a: array<int>) returns (sorted: bool)
{
  sorted := true;
  if a.Length <= 1 {
    return;
  }
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant sorted ==> forall j :: 0 <= j < i ==> a[j] <= a[j + 1]
  {
    if a[i] > a[i + 1] {
      sorted := false;
      return;
    }
    i := i + 1;
  }
}