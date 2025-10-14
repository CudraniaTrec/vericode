method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
{
    if (a <= b && a <= c) {
        assert a <= b && a <= c;
        min := a;
        assert min == a;
        assert min <= a && min <= b && min <= c;
        assert (min == a) || (min == b) || (min == c);
    } else if (b <= a && b <= c) {
        assert !(a <= b && a <= c);
        assert b <= a && b <= c;
        min := b;
        assert min == b;
        assert min <= a && min <= b && min <= c;
        assert (min == a) || (min == b) || (min == c);
    } else {
        assert !(a <= b && a <= c);
        assert !(b <= a && b <= c);
        min := c;
        assert min == c;
        assert min <= a && min <= b && min <= c;
        assert (min == a) || (min == b) || (min == c);
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
