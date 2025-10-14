method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
    ensures sum == (set d | 1 <= d <= if a < b then a else b && a % d == 0 && b % d == 0 :: d).Sum
{
    var min_ab := if a < b then a else b;
    sum := 0;
    var d := 1;
    while d <= min_ab
        invariant 1 <= d <= min_ab + 1
        invariant sum == (set x | 1 <= x < d && a % x == 0 && b % x == 0 :: x).Sum
    {
        if a % d == 0 && b % d == 0 {
            sum := sum + d;
        }
        d := d + 1;
    }
}