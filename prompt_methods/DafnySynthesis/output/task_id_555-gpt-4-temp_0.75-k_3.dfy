// Dafny Code

method SumCubeDifference(n: nat) returns (diff: int)
    ensures diff == (sum i | 1 <= i <= n :: i * i * i) - (sum i | 1 <= i <= n :: i)
{
    var sumCubes := 0;
    var sumNums := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant sumCubes == (sum j | 1 <= j < i :: j * j * j)
        invariant sumNums == (sum j | 1 <= j < i :: j)
    {
        sumCubes := sumCubes + i * i * i;
        sumNums := sumNums + i;
        i := i + 1;
    }
    diff := sumCubes - sumNums;
}