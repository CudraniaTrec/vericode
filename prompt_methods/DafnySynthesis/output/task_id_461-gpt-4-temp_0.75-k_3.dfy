method CountUpperCaseCharacters(s: string) returns (count: nat)
    ensures 0 <= count <= |s|
    ensures count == |[i | i := 0 .. |s|, 'A' <= s[i] <= 'Z']|
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= count <= i
        invariant count == |[j | j := 0 .. i, 'A' <= s[j] <= 'Z']|
    {
        if 'A' <= s[i] <= 'Z' {
            count := count + 1;
        }
        i := i + 1;
    }
}