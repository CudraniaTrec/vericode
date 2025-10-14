method ToUpperCase(s: string) returns (res: string)
{
  var chars := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant chars[..i] == (seq j | 0 <= j < i :: 
        if 'a' <= s[j] <= 'z' then 
            (s[j] as int + ('A' as int - 'a' as int)) as char 
        else 
            s[j])
  {
    var c := s[i];
    if 'a' <= c <= 'z' {
      chars[i] := (c as int + ('A' as int - 'a' as int)) as char;
    } else {
      chars[i] := c;
    }
    i := i + 1;
  }
  res := string(chars);
}