
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    // Invariant: 1 <= i <= n+1
    // sumCubes == sum_{k=1}^{i-1} k^3
    // sumNumbers == sum_{k=1}^{i-1} k
    for i := 1 to n + 1
        invariant 1 <= i <= n + 1 + 1
        invariant sumCubes == (i - 1) * i / 2 * (i - 1) * i / 2
        invariant sumNumbers == ((i - 1) * i) / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
        assert sumCubes == (i * (i + 1) / 2) * (i * (i + 1) / 2);
        assert sumNumbers == (i * (i + 1)) / 2;
    }
    // At this point, i == n+1+1, so sumCubes == (n+1)^2*(n+1)^2/4, sumNumbers == (n+1)*(n+2)/2
    diff := sumCubes - sumNumbers;
    assert sumCubes == ((n + 1) * (n + 2) / 2) * ((n + 1) * (n + 2) / 2);
    assert sumNumbers == ((n + 1) * (n + 2)) / 2;
    assert diff == ((n + 1) * (n + 2) / 2) * ((n + 1) * (n + 2) / 2) - ((n + 1) * (n + 2)) / 2;
    // But we want to show diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
    // Actually, the loop runs from 1 to n+1, so sum up to n+1, not n.
}

function abs(a: real) : real {if a>0.0 then a else -a}
