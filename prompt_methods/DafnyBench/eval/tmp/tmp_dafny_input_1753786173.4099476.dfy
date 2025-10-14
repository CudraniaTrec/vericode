
// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
    var l, r := 0, x;
    while (l <= r)
        invariant 0 <= l <= x+1
        invariant -1 <= r <= x
        invariant l <= r+1
        invariant forall k :: 0 <= k < l ==> k*k <= x && (k+1)*(k+1) <= x
        invariant forall k :: r < k <= x ==> k*k > x
        decreases r - l + 1
    {
        var mid := (l + r) / 2;
        assert l <= mid <= r;
        if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
            assert sqrt(x, mid);
            return mid;
        } else if (mid * mid <= x) {
            l := mid + 1;
        } else {
            r := mid - 1;
        }
    }
    // Should never reach here for x >= 0
    assert false;
}

function abs(a: real) : real {if a>0.0 then a else -a}
