method ReplaceWithColon(s: string) returns (res: string)
{
    var chars := new seq<char>(s.Length);
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant chars.Length == i
        invariant forall j :: 0 <= j < i ==> chars[j] == (if s[j] == ' ' || s[j] == ',' || s[j] == '.' then ':' else s[j])
    {
        if s[i] == ' ' || s[i] == ',' || s[i] == '.' {
            chars := chars + [':'];
        } else {
            chars := chars + [s[i]];
        }
        i := i + 1;
    }
    res := string(chars);
}