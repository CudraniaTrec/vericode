method ContainsAThenTwoOrThreeBs(s: string) returns (found: bool)
{
  found := false;
  var n := s.Length;
  // Look for 'a' at position i, followed by "bb" or "bbb"
  var i: int := 0;
  while i <= n - 3 // need at least 'a' + "bb"
    invariant 0 <= i <= n - 2
    decreases n - i
  {
    if s[i] == 'a' && s[i+1] == 'b' && s[i+2] == 'b' {
      // Check for two or three 'b's
      if i+3 < n && s[i+3] == 'b' {
        found := true;
        return;
      } else {
        found := true;
        return;
      }
    }
    i := i + 1;
  }
  // Special case: if only two 'b's fit at the end
  if i == n - 2 && s[i] == 'a' && s[i+1] == 'b' && s[i+2] == 'b' {
    found := true;
    return;
  }
}