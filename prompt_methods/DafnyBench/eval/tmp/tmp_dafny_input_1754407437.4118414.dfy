method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    assert 0 <= d < 32;
    assert (n << d) == n << d;
    assert (n >> (32 - d)) == n >> (32 - d);
    result := ((n << d) | (n >> (32 - d)));
    assert result == ((n << d) | (n >> (32 - d)));
}
function abs(a: real) : real {if a>0.0 then a else -a}
