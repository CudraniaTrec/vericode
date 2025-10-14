//Dafny Code

method SwapFirstAndLast(a: array<int>)
  requires a != null && a.Length >= 1
  modifies a
{
  if a.Length > 1 {
    var temp := a[0];
    a[0] := a[a.Length - 1];
    a[a.Length - 1] := temp;
  }
}