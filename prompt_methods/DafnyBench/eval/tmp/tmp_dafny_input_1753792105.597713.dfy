method IsOdd(n: int) returns (result: bool)
    ensures result <==> n % 2 == 1
{
    // n % 2 == 1 if and only if n is odd
    assert n % 2 == 1 ==> n % 2 == 1;
    assert n % 2 != 1 ==> n % 2 != 1;
    result := n % 2 == 1;
    assert result <==> n % 2 == 1;
}
function abs(a: real) : real {if a>0.0 then a else -a}
