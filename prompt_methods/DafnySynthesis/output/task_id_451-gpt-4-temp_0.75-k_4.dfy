method RemoveWhitespaces(s: string) returns (res: string)
{
    var chars := new seq<char>();
    var i := 0;
    while i < |s|
        decreases |s| - i
    {
        if s[i] != ' ' && s[i] != '\t' && s[i] != '\n' && s[i] != '\r'
        {
            chars := chars + [s[i]];
        }
        i := i + 1;
    }
    res := chars[..].AsString();
}