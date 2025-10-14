method BellNumber(n: nat) returns (bn: nat)
    // Computes the nth Bell number: number of ways to partition a set of size n
{
    var dp := new nat[n+1, n+1];
    dp[0, 0] := 1;
    // Fill the dp table using Bell's triangle
    var i := 1;
    while i <= n
        invariant 0 <= i <= n+1
        invariant forall x :: 0 <= x < i ==> dp[x, 0] == dp[x-1, x-1] || x == 0
        decreases n + 1 - i
    {
        dp[i, 0] := dp[i-1, i-1];
        var j := 1;
        while j <= i
            invariant 0 <= j <= i
            decreases i - j
        {
            dp[i, j] := dp[i-1, j-1] + dp[i, j-1];
            j := j + 1;
        }
        i := i + 1;
    }
    bn := dp[n,0];
}