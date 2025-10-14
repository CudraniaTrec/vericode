// Dafny Code

method SumFourthPowerFirstNOdd(n: nat) returns (sum: nat)
    ensures sum == (forall k :: 1 <= k <= n ==> (2*k - 1)*(2*k - 1)*(2*k - 1)*(2*k - 1)) .Sum
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (forall k :: 1 <= k < i ==> (2*k - 1)*(2*k - 1)*(2*k - 1)*(2*k - 1)) .Sum
    {
        var odd := 2 * i - 1;
        sum := sum + odd * odd * odd * odd;
        i := i + 1;
    }
}