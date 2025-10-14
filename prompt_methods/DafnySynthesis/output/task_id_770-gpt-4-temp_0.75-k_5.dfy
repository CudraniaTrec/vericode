//Dafny Code

method SumFourthPowerOddNumbers(n: nat) returns (sum: nat)
    ensures sum == (forall i :: 0 <= i < n ==> (2*i + 1) * (2*i + 1) * (2*i + 1) * (2*i + 1)) // For clarity
    decreases n
{
    sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum == (forall j :: 0 <= j < i ==> (2*j+1)*(2*j+1)*(2*j+1)*(2*j+1))
    {
        var odd := 2*i + 1;
        sum := sum + odd * odd * odd * odd;
        i := i + 1;
    }
}