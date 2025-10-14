// Dafny Code

method ContainsDuplicate(a: array<int>) returns (hasDuplicate: bool)
{
  hasDuplicate := false;
  var n := a.Length;
  // Iterate through each pair of elements
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall x, y :: 0 <= x < y < i ==> a[x] != a[y]
    decreases n - i
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant forall k :: i + 1 <= k < j ==> a[i] != a[k]
      decreases n - j
    {
      if a[i] == a[j] {
        hasDuplicate := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}