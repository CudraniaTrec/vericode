method ToLowerCase(s: string) returns (res: string)
  ensures res == s.ToLower()
{
    var chars := new char[s.Length];
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall j :: 0 <= j < i ==> chars[j] == if 'A' <= s[j] <= 'Z' then (char)(s[j] as int + 32) else s[j]
    {
        if 'A' <= s[i] <= 'Z' {
            chars[i] := (char)(s[i] as int + 32);
        } else {
            chars[i] := s[i];
        }
        i := i + 1;
    }
    res := string(chars);
}