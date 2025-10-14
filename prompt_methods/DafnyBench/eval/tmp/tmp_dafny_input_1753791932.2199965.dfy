method StarNumber(n: int) returns (star: int)
    requires n >= 0
    ensures star == 6 * n * (n - 1) + 1
{
    // n >= 0
    // star = 6 * n * (n - 1) + 1
    assert n >= 0;
    star := 6 * n * (n - 1) + 1;
    assert star == 6 * n * (n - 1) + 1;
}
function abs(a: real) : real {if a>0.0 then a else -a}
