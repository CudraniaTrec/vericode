method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    // Strongest annotation: The shift amounts are within bounds for bv32
    assert 0 <= d < 32;
    assert 0 < 32 - d <= 32;
    result := ((n << d) | (n >> (32 - d)));
    assert result == ((n << d) | (n >> (32 - d)));
}
function abs(a: real) : real {if a>0.0 then a else -a}
