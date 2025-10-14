method Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
{
    if a <= b {
        assert a <= b;
        minValue := a;
        assert minValue == a;
        assert minValue == a || minValue == b;
        assert minValue <= a && minValue <= b;
    } else {
        assert a > b;
        minValue := b;
        assert minValue == b;
        assert minValue == a || minValue == b;
        assert minValue <= a && minValue <= b;
    }
    assert minValue == a || minValue == b;
    assert minValue <= a && minValue <= b;
}
function abs(a: real) : real {if a>0.0 then a else -a}
