method SwapFirstAndLast(a: array<int>)
  requires a != null && a.Length >= 2
  modifies a
{
  var temp := a[0];
  a[0] := a[a.Length - 1];
  a[a.Length - 1] := temp;
}