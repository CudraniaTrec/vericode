method FirstRepeatedChar(s: string) returns (found: bool, ch: char)
{
  var seen := set char{};
  var i: int := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j: int :: 0 <= j < i ==> s[j] in seen
    invariant |seen| <= i
  {
    if s[i] in seen {
      found, ch := true, s[i];
      return;
    }
    seen := seen + {s[i]};
    i := i + 1;
  }
  found, ch := false, '\0';
}