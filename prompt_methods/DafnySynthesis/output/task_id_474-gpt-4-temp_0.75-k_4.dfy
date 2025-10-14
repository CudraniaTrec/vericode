method ReplaceChars(s: string, oldChar: char, newChar: char) returns (result: string)
    ensures result.Length == s.Length
    ensures forall i :: 0 <= i < s.Length ==> 
        result[i] == if s[i] == oldChar then newChar else s[i]
{
    var builder := new System.Text.StringBuilder();
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant builder.Length == i
        invariant forall j :: 0 <= j < i ==> 
            builder.ToString()[j] == (if s[j] == oldChar then newChar else s[j])
    {
        if s[i] == oldChar {
            builder.Append(newChar);
        } else {
            builder.Append(s[i]);
        }
        i := i + 1;
    }
    result := builder.ToString();
}