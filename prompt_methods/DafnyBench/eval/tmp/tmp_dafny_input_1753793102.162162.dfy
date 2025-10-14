
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    sum := 0;
    var i := 1;
    // Invariant: after k iterations, i == 2*k + 1, sum == sum of (2*j+1)^4 for j in 0..k-1
    for k := 0 to n
        invariant 0 <= k <= n
        invariant i == 2 * k + 1
        invariant sum == (if k == 0 then 0 else (k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7)) / 15)
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
    assert i == 2 * (n + 1) + 1;
    assert sum == (n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7)) / 15;
}

function abs(a: real) : real {if a>0.0 then a else -a}
