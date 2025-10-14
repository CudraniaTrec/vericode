//Dafny Code

method SumOfSquaresOfEvenNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == 4 * n * (n + 1) * (2*n + 1) / 6
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant sum == 4 * (i-1) * i * (2*(i-1) + 1) / 6
    {
        var even := 2 * i;
        sum := sum + even * even;
        i := i + 1;
    }
}