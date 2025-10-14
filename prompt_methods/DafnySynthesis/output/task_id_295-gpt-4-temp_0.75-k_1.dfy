method SumOfDivisors(n: nat) returns (sum: nat)
    requires n > 0
    ensures sum == (sum i | 1 <= i <= n && n % i == 0 :: i)
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (sum j | 1 <= j < i && n % j == 0 :: j)
    {
        if n % i == 0 {
            sum := sum + i;
        }
        i := i + 1;
    }
}