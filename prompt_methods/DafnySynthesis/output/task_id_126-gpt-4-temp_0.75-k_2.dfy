method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
    ensures sum == (sum d | 1 <= d <= if a < b then a else b && a % d == 0 && b % d == 0 :: d)
{
    var minValue := if a < b then a else b;
    sum := 0;
    var d := 1;
    while d <= minValue
        invariant 1 <= d <= minValue + 1
        invariant sum == (sum k | 1 <= k < d && a % k == 0 && b % k == 0 :: k)
    {
        if a % d == 0 && b % d == 0 {
            sum := sum + d;
        }
        d := d + 1;
    }
}