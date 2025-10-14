method ReplaceSpaces(s: string) returns (res: string)
{
    var builder := new seq<char>();
    var n := s.Length;
    var i := 0;
    while i < n
        decreases n - i
    {
        if s[i] == ' ' {
            builder := builder + ['%', '2', '0'];
        } else {
            builder := builder + [s[i]];
        }
        i := i + 1;
    }
    res := string(builder);
}