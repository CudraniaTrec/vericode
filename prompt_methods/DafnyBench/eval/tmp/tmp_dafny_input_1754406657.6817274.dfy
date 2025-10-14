
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{
    // The median is the value that is neither the maximum nor the minimum of the three.
    // There are 6 possible orderings; the following cases cover all.
    if ((a <= b && b <= c) || (c <= b && b <= a)) {
        assert (a <= b && b <= c) || (c <= b && b <= a);
        assert b == a || b == b || b == c; // b is one of the three
        median := b;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    } else if ((b <= a && a <= c) || (c <= a && a <= b)) {
        assert (b <= a && a <= c) || (c <= a && a <= b);
        assert a == a || a == b || a == c; // a is one of the three
        median := a;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    } else {
        assert !((a <= b && b <= c) || (c <= b && b <= a));
        assert !((b <= a && a <= c) || (c <= a && a <= b));
        // The only remaining case is that c is the median
        median := c;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
