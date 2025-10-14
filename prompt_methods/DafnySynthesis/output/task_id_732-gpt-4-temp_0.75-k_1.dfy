method ReplaceWithColon(s: string) returns (res: string)
{
  var builder := new string[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant builder[..i] == (s[..i]).Map(lambda c: if c == ' ' || c == ',' || c == '.' then ':' else c)
  {
    if s[i] == ' ' || s[i] == ',' || s[i] == '.' {
      builder[i] := ':';
    } else {
      builder[i] := s[i];
    }
    i := i + 1;
  }
  res := builder;
}