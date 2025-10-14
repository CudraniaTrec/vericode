method SumOfSquaresOfOddNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (if n == 0 then 0 else sum i: int | 1 <= i <= n :: (2*i - 1)*(2*i - 1))
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == sum j: int | 1 <= j < i :: (2*j - 1)*(2*j - 1)
    {
        sum := sum + (2*i - 1)*(2*i - 1);
        i := i + 1;
    }
}