method SumEvenPowersOfFive(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (
        var s := 0;
        var i := 1;
        while i <= n
            invariant 1 <= i <= n + 1
            invariant s == (if i > 1 then (2 * (i-1)) ^ 5 + ... + (2*1)^5 else 0)
        {
            s := s + (2 * i) ^ 5;
            i := i + 1;
        }
        s
    )
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (if i > 1 then (2 * (i-1)) ^ 5 + ... + (2*1)^5 else 0)
    {
        sum := sum + (2 * i) ^ 5;
        i := i + 1;
    }
}