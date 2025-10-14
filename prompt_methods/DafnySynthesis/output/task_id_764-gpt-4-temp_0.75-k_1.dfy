// Dafny Code

method CountDigits(s: string) returns (count: int)
    ensures 0 <= count <= |s|
    ensures count == |s| - |[i := 0 .. |s| - 1 :: s[i] < '0' || s[i] > '9']|
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= count <= i
        invariant count == |[j := 0 .. i-1 :: '0' <= s[j] <= '9']|
    {
        if '0' <= s[i] <= '9' {
            count := count + 1;
        }
        i := i + 1;
    }
}