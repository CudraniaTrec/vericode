method ToLowerCase(s: string) returns (res: string)
{
    var chars := new char[s.Length];
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant chars.Length == s.Length
        invariant forall j :: 0 <= j < i ==> chars[j] == 
            if 'A' <= s[j] <= 'Z' then
                char#('a' + (s[j] as int - 'A' as int))
            else
                s[j]
    {
        if 'A' <= s[i] <= 'Z' {
            chars[i] := char#('a' + (s[i] as int - 'A' as int));
        } else {
            chars[i] := s[i];
        }
        i := i + 1;
    }
    res := string(chars);
}