
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{
    // The median is the value that is neither the maximum nor the minimum of the three.
    // There are 6 possible orderings of a, b, c.

    if ((a <= b && b <= c) || (c <= b && b <= a)) {
        assert (a <= b && b <= c) || (c <= b && b <= a);
        assert (b == a || b == c || (a < b && b < c) || (c < b && b < a));
        median := b;
        assert median == b;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    } else if ((b <= a && a <= c) || (c <= a && a <= b)) {
        assert (b <= a && a <= c) || (c <= a && a <= b);
        assert (a == b || a == c || (b < a && a < c) || (c < a && a < b));
        median := a;
        assert median == a;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    } else {
        assert !((a <= b && b <= c) || (c <= b && b <= a));
        assert !((b <= a && a <= c) || (c <= a && a <= b));
        // The only remaining cases are where c is the median
        median := c;
        assert median == c;
        assert median == a || median == b || median == c;
        assert (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
