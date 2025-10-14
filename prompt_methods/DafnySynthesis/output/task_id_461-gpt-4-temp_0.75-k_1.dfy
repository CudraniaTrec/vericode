method CountUpperCaseCharacters(s: string) returns (count: nat)
{
    count := 0;
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == (|[j | 0 <= j < i && 'A' <= s[j] <= 'Z' ]|)
    {
        if 'A' <= s[i] <= 'Z' {
            count := count + 1;
        }
        i := i + 1;
    }
}