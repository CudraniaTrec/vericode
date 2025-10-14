method MoveNumbersToEnd(s: string) returns (res: string)
    ensures |res| == |s|
    ensures (forall i :: 0 <= i < |res| ==> (res[i] in {'0','1','2','3','4','5','6','7','8','9'}) <==> (|s| - |res| + i < |s| && s[|s| - |res| + i] in {'0','1','2','3','4','5','6','7','8','9'}))
    ensures multiset(res) == multiset(s)
{
    var nonDigits := "";
    var digits := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |nonDigits| + |digits| == i
        invariant multiset(nonDigits + digits) == multiset(s[..i])
        decreases |s| - i
    {
        if '0' <= s[i] <= '9' {
            digits := digits + s[i].ToString();
        } else {
            nonDigits := nonDigits + s[i].ToString();
        }
        i := i + 1;
    }
    res := nonDigits + digits;
}