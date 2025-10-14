method SumOfOddSquares(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (forall i :: 1 <= i <= n ==> (2 * i - 1) * (2 * i - 1)).FoldLeft(0, (acc, x) => acc + x)
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant sum == (forall j :: 1 <= j < i ==> (2 * j - 1) * (2 * j - 1)).FoldLeft(0, (acc, x) => acc + x)
    {
        sum := sum + (2 * i - 1) * (2 * i - 1);
        i := i + 1;
    }
}