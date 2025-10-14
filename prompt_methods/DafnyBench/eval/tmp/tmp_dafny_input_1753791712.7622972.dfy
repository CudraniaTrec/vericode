
method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
{
    sum := 0;
    var i := 1;
    while i <= a && i <= b
        invariant 1 <= i <= a + 1 && 1 <= i <= b + 1
        invariant sum == (if i == 1 then 0 else sumCommonDivisors(a, b, i - 1))
        invariant sum >= 0
    {
        if a % i == 0 && b % i == 0 {
            sum := sum + i;
        }
        i := i + 1;
    }
    // At loop exit: i > a || i > b
    // The maximum possible common divisor is min(a, b)
    // sum == sumCommonDivisors(a, b, min(a, b))
    // assert sum == sumCommonDivisors(a, b, if a < b then a else b);
}

function sumCommonDivisors(a: int, b: int, k: int): int
    requires a > 0 && b > 0 && k >= 0
    decreases k
{
    if k == 0 then 0
    else sumCommonDivisors(a, b, k - 1) + (if a % k == 0 && b % k == 0 then k else 0)
}

function abs(a: real) : real {if a>0.0 then a else -a}
