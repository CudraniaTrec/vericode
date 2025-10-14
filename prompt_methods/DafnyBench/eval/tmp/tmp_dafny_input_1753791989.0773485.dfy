method Quotient(a: int, b: int) returns (result: int)
    requires b != 0
    ensures result == a / b
{
    assert b != 0;
    result := a / b;
    assert result == a / b;
}
function abs(a: real) : real {if a>0.0 then a else -a}
