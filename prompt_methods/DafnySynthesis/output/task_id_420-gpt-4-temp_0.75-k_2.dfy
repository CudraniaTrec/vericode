// Dafny Code

method CubeSumFirstNEvenNumbers(n: nat) returns (sum: nat)
    ensures sum == (2*n*(n + 1))*(2*n*(n + 1))/4
{
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (2 * ((i-1)) * (i)) * (2 * ((i-1)) * (i)) / 4
    {
        var evenNum := 2 * i;
        sum := sum + evenNum * evenNum * evenNum;
        i := i + 1;
    }
}