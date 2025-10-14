method replaceBlank(str1:string, ch:char) returns (res:string)
{
    var chars := new char[str1.Length];
    var i := 0;
    while i < str1.Length
        invariant 0 <= i <= str1.Length
        invariant chars[..i] == (seq j | 0 <= j < i :: if str1[j] == ' ' then ch else str1[j])
    {
        if str1[i] == ' ' {
            chars[i] := ch;
        } else {
            chars[i] := str1[i];
        }
        i := i + 1;
    }
    res := string(chars);
}