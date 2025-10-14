// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{
    if r1 != r2 {
        if r1 < r2 {
            assert r2 >= r1 + 1;
            assert (r1+1)*(r1+1) > x;
            assert r2*r2 <= x;
            assert (r2*r2) >= ((r1+1)*(r1+1));
            assert false;
        } else {
            assert r1 >= r2 + 1;
            assert (r2+1)*(r2+1) > x;
            assert r1*r1 <= x;
            assert (r1*r1) >= ((r2+1)*(r2+1));
            assert false;
        }
    }
}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
    var l, r := 0, x;
    // The loop searches for the largest mid such that mid*mid <= x
    while (l <= r)
        invariant 0 <= l && r <= x
        invariant 0 <= l && l <= x+1
        invariant -1 <= r && r <= x
        invariant forall k :: 0 <= k < l ==> k*k > x
        invariant forall k :: r < k <= x ==> k*k <= x ==> false
        decreases r - l + 1
    {
        var mid := (l + r) / 2;
        if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
            res := mid;
            return;
        } else if (mid * mid <= x) {
            l := mid + 1;
        } else {
            r := mid - 1;
        }
    }
    // After the loop, l > r. The only possible value for res is r.
    res := r;
    // Prove postcondition
    assert res*res <= x;
    assert (res+1)*(res+1) > x;
}

function abs(a: real) : real {if a>0.0 then a else -a}
