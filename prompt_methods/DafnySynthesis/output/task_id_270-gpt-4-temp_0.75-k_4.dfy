method SumEvenAtEvenPositions(a: array<int>) returns (sum: int)
  ensures 0 <= sum
  ensures sum == (if a == null then 0 else
    var s := 0;
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant s == (sum j | 0 <= j < i && j % 2 == 0 && a[j] % 2 == 0 :: a[j])
    {
      if i % 2 == 0 && a[i] % 2 == 0 {
        s := s + a[i];
      }
      i := i + 1;
    }
    s)
{
  sum := 0;
  if a == null {
    return;
  }
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == (sum j | 0 <= j < i && j % 2 == 0 && a[j] % 2 == 0 :: a[j])
  {
    if i % 2 == 0 && a[i] % 2 == 0 {
      sum := sum + a[i];
    }
    i := i + 1;
  }
}