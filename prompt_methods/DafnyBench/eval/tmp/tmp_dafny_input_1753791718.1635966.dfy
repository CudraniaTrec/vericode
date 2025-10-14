
method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{
    sum := 0;
    var i := 1;
    while i <= if a < b then a else b
        invariant 1 <= i <= (if a < b then a else b) + 1
        invariant sum >= 0
        invariant forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
    {
        if a % i == 0 && b % i == 0 {
            sum := sum + i;
        }
        i := i + 1;
    }
    // After the loop: forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
    // i = min(a, b) + 1, so d ranges over all possible common divisors in [1, min(a, b)]
    // So postcondition holds
}

function abs(a: real) : real {if a>0.0 then a else -a}
