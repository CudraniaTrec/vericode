method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    // Loop invariant: for all 1 <= i <= n+1, after i-1 iterations,
    // sumCubes == sum_{k=1}^{i-1} k^3
    // sumNumbers == sum_{k=1}^{i-1} k
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sumCubes == ((i - 1) * (i - 1) * i * i) / 4
        invariant sumNumbers == ((i - 1) * i) / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
        i := i + 1;
    }
    // After the loop: i == n+1
    // sumCubes == (n * n * (n + 1) * (n + 1)) / 4
    // sumNumbers == (n * (n + 1)) / 2
    assert sumCubes == (n * n * (n + 1) * (n + 1)) / 4;
    assert sumNumbers == (n * (n + 1)) / 2;
    diff := sumCubes - sumNumbers;
}
function abs(a: real) : real {if a>0.0 then a else -a}
