method ToggleCase(s: string) returns (toggled: string)
{
  var chars := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant chars[..i] == [ if 'a' <= s[i0] <= 'z' then (s[i0] as int - 32) as char
                              else if 'A' <= s[i0] <= 'Z' then (s[i0] as int + 32) as char
                              else s[i0]
                              | i0 <- 0..i-1 ]
  {
    var c := s[i];
    if 'a' <= c <= 'z' {
      chars[i] := (c as int - 32) as char;
    } else if 'A' <= c <= 'Z' {
      chars[i] := (c as int + 32) as char;
    } else {
      chars[i] := c;
    }
    i := i + 1;
  }
  toggled := string(chars);
}