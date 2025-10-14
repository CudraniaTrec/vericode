method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
{
    if a >= b {
        assert a >= b;
        maxValue := a;
        assert maxValue == a || maxValue == b;
        assert maxValue >= a && maxValue >= b;
    } else {
        assert b > a;
        maxValue := b;
        assert maxValue == a || maxValue == b;
        assert maxValue >= a && maxValue >= b;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
