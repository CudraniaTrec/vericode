// Dafny Code

method isProductEven(arr:array<int>) returns (res:bool)
  requires arr != null
{
  var n := arr.Length;
  res := false;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res ==> exists j :: 0 <= j < i && arr[j] % 2 == 0
    decreases n - i
  {
    if arr[i] % 2 == 0 {
      res := true;
      return;
    }
    i := i + 1;
  }
  // If no even element found, product is odd
  res := false;
}