
method SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    sum := 0;
    var i := 1;
    var k: int;
    // Invariant: sum == k * (2 * k - 1) * (2 * k + 1) / 3
    //            && i == 2 * k + 1
    //            && 0 <= k <= n
    //            && forall j :: 0 <= j < k ==> (sum == sum of squares of first k odd numbers)
    for k := 0 to n
        invariant 0 <= k <= n
        invariant i == 2 * k + 1
        invariant sum == (k * (2 * k - 1) * (2 * k + 1)) / 3
    {
        sum := sum + i * i;
        i := i + 2;
        // assert sum == ((k+1) * (2 * (k+1) - 1) * (2 * (k+1) + 1)) / 3 - (i*i); // optional
    }
    // assert sum == (n * (2 * n - 1) * (2 * n + 1)) / 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
