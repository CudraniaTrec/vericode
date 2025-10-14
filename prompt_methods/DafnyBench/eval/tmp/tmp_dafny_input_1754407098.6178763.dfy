
method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
{
    sum := 0;
    var i: int := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (i - 1) * i / 2
    {
        sum := sum + i;
        i := i + 1;
    }
    assert i == n + 1;
    assert sum == n * (n + 1) / 2;
    average := sum as real / n as real;
}

function abs(a: real) : real {if a>0.0 then a else -a}
