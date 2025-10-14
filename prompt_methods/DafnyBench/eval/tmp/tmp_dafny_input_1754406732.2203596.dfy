method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
    d := n % 10;
    assert 0 <= d < 10;
    assert n % 10 == d;
}
function abs(a: real) : real {if a>0.0 then a else -a}
