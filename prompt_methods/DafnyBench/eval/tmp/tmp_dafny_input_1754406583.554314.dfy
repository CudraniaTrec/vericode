
method SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    sum := 0;
    var i := 1;
    // Loop invariant: k <= n
    // Loop invariant: i == 1 + 2 * k
    // Loop invariant: sum == k * (2 * k - 1) * (2 * k + 1) / 3
    // Loop invariant: 0 <= k <= n
    for k:=0 to n
        invariant 0 <= k <= n
        invariant i == 1 + 2 * k
        invariant sum == (k * (2 * k - 1) * (2 * k + 1)) / 3
    {
        sum := sum + i * i;
        i := i + 2;
        // assert sum == ((k+1) * (2 * (k+1) - 1) * (2 * (k+1) + 1)) / 3;
    }
    // assert sum == (n * (2 * n - 1) * (2 * n + 1)) / 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
