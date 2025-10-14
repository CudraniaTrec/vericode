method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
    // n >= 0 by precondition
    d := n % 10;
    assert 0 <= d < 10; // Because n >= 0, n % 10 is in [0,9]
    assert n % 10 == d;
}
function abs(a: real) : real {if a>0.0 then a else -a}
