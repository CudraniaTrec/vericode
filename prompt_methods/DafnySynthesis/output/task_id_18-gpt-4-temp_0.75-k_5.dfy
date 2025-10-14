method RemoveChars(s: string, remove: string) returns (result: string)
    ensures result == s[..].Filter(c => !(remove[..].Contains(c))).AsString()
{
    var removeSet := remove[..].ToSet();
    var builder := new seq<char>[];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant builder.AsSeq() == s[..i].Filter(c => !(removeSet.Contains(c)))
    {
        if !(removeSet.Contains(s[i])) {
            builder := builder + [s[i]];
        }
        i := i + 1;
    }
    result := builder.AsSeq().AsString();
}