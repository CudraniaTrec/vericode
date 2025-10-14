method SumFirstNEvenFifthPowers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (if n == 0 then 0 else (var total := 0; var i := 1; while i <= n invariant 1 <= i <= n + 1 invariant total == (if i == 1 then 0 else total); i := i + 1 { total := total + (2 * i - 2) * (2 * i - 2) * (2 * i - 2) * (2 * i - 2) * (2 * i - 2); }; total))
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (if i == 1 then 0 else sum)
    {
        var even := 2 * i;
        sum := sum + even * even * even * even * even;
        i := i + 1;
    }
}