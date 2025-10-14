
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
        invariant 0 <= l && l <= x+1
        invariant -1 <= r && r <= x
        invariant l <= r+1
        invariant forall k :: 0 <= k < l ==> (k * k <= x)
        invariant forall k :: r < k <= x ==> (k * k > x)
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
    // l > r at this point, so r < l and r >= -1
    // The unique r in [0..x] such that r*r <= x < (r+1)*(r+1) is r = r
    // So, r is the integer square root
    res := r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
