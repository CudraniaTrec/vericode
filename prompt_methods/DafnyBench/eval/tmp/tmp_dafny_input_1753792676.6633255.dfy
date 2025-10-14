method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
{
    assert n % 2 == 0 <==> (n % 2 == 0);
    result := n % 2 == 0;
    assert result <==> n % 2 == 0;
}
function abs(a: real) : real {if a>0.0 then a else -a}
