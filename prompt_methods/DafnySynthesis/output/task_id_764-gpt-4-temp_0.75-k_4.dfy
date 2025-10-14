method CountDigits(s: string) returns (count: nat)
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == (|{ j: int | 0 <= j < i && '0' <= s[j] <= '9' }|)
    {
        if '0' <= s[i] <= '9' {
            count := count + 1;
        }
        i := i + 1;
    }
}