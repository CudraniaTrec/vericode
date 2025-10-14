method replaceBlank(str1:string, ch:char) returns (res:string)
{
    var n := |str1|;
    var builder := new seq<char>[];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |builder| == i
        invariant forall j :: 0 <= j < i ==> builder[j] == (if str1[j] == ' ' then ch else str1[j])
    {
        if str1[i] == ' ' {
            builder := builder + [ch];
        } else {
            builder := builder + [str1[i]];
        }
        i := i + 1;
    }
    res := builder[..];
}