method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    var i := 1;
    while i <= n + 1
        invariant 1 <= i <= n + 2
        invariant sumCubes == ((i - 1) * i / 2) * ((i - 1) * i / 2)
        invariant sumNumbers == ((i - 1) * i) / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
        i := i + 1;
    }
    // At this point, i == n + 2
    // sumCubes == (n+1)*n/2 * (n+1)*n/2 = (n*(n+1)/2)^2
    // sumNumbers == (n+1)*n/2
    assert i == n + 2;
    assert sumCubes == (n * (n + 1) / 2) * (n * (n + 1) / 2);
    assert sumNumbers == (n * (n + 1)) / 2;
    diff := sumCubes - sumNumbers;
}
function abs(a: real) : real {if a>0.0 then a else -a}
