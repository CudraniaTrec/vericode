method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    // Both a and b are positive
    assert a > 0;
    assert b > 0;
    // (a + b) is at least 2
    assert a + b >= 2;
    median := (a + b) / 2;
    // median is assigned correctly
    assert median == (a + b) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
