function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    var i := 1;
    res := 1;
    while i < n + 1 
        invariant 1 <= i <= n + 1
        invariant res == fact(i - 1)
        invariant res >= 1
    {
        res := i * res;
        i := i + 1;
    }
    assert i == n + 1;
    assert res == fact(n);
}
function abs(a: real) : real {if a>0.0 then a else -a}
