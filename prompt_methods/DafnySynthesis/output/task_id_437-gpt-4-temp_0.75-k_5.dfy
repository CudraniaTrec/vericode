method RemoveOddCharacters(s: string) returns (t: string)
    ensures t == StringFromSeq([s[i] | i := 0 .. |s|, i % 2 == 0])
{
    var chars := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant chars == [s[j] | j := 0 .. i, j % 2 == 0]
    {
        if i % 2 == 0 {
            chars := chars + [s[i]];
        }
        i := i + 1;
    }
    t := StringFromSeq(chars);
}