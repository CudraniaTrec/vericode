method InsertSpacesBetweenCapitalWords(s: string) returns (res: string)
{
    var n := s.Length;
    var r := "";
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant r.Length <= i + r.Length - r.Length
    {
        if i > 0 && 'A' <= s[i] <= 'Z' && s[i-1] != ' ' {
            r := r + " ";
        }
        r := r + s[i..i+1];
        i := i + 1;
    }
    res := r;
}