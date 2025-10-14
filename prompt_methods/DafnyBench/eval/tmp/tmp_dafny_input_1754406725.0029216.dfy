method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    // Strongest annotation: both a and b are positive
    assert a > 0;
    assert b > 0;
    // (a + b) is positive and even/odd, integer division is safe
    assert a + b > 0;
    median := (a + b) / 2;
    assert median == (a + b) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
