method ReplaceChar(s: string, oldChar: char, newChar: char) returns (result: string)
    ensures result.Length == s.Length
    ensures forall i :: 0 <= i < s.Length ==> result[i] == (if s[i] == oldChar then newChar else s[i])
{
    var builder := new seq<char>([]);
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant builder.Length == i
        invariant forall j :: 0 <= j < i ==> builder[j] == (if s[j] == oldChar then newChar else s[j])
    {
        var ch := s[i];
        if ch == oldChar {
            builder := builder + [newChar];
        } else {
            builder := builder + [ch];
        }
        i := i + 1;
    }
    result := builder[..];
}