method ContainsAThenTwoOrThreeBs(s: string) returns (found: bool)
{
  found := false;
  var n := s.Length;
  // Check for 'a' followed by 'bb' or 'bbb'
  // Need to check positions 0..n-3 for "abb" and 0..n-4 for "abbb"
  var i := 0;
  while i <= n - 3
    invariant 0 <= i <= n - 3 + 1
    invariant forall j :: 0 <= j < i ==> 
      !((s[j] == 'a' && s[j+1] == 'b' && s[j+2] == 'b') ||
        (j <= n - 4 && s[j] == 'a' && s[j+1] == 'b' && s[j+2] == 'b' && s[j+3] == 'b'))
  {
    if s[i] == 'a' && s[i+1] == 'b' && s[i+2] == 'b' {
      found := true;
      return;
    }
    if i <= n - 4 && s[i] == 'a' && s[i+1] == 'b' && s[i+2] == 'b' && s[i+3] == 'b' {
      found := true;
      return;
    }
    i := i + 1;
  }
}