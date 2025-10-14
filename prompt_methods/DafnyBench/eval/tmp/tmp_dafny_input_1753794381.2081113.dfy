
method main(n: int) returns (sum: int, i: int)
requires n >= 0
{
    sum := 0;
    i := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant sum == i * (i - 1) / 2
        invariant sum >= 0
    {
        sum := sum + i;
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
