method CountSubstringsSumEqualsLength(s: string) returns (count: int)
  ensures 0 <= count <= |s| * (|s| + 1) / 2
{
  count := 0;
  var n := |s|;
  var digits := new int[n];
  // Precompute digits
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant digits[..i] == [s[j] as int - '0' as int | j := 0 .. i]
  {
    digits[i] := s[i] as int - '0' as int;
    i := i + 1;
  }
  // Compute prefix sums
  var prefix := new int[n + 1];
  prefix[0] := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j <= i ==> prefix[j+1] == prefix[j] + digits[j]
  {
    prefix[i+1] := prefix[i] + digits[i];
    i := i + 1;
  }
  // Check all substrings
  var l := 0;
  while l < n
    invariant 0 <= l <= n
    invariant 0 <= count <= l * n - l * (l - 1) / 2 // conservative upper bound
  {
    var r := l;
    while r < n
      invariant l <= r <= n
      invariant 0 <= count <= n * (n + 1) / 2
    {
      var sum := prefix[r+1] - prefix[l];
      var len := r - l + 1;
      if sum == len {
        count := count + 1;
      }
      r := r + 1;
    }
    l := l + 1;
  }
}