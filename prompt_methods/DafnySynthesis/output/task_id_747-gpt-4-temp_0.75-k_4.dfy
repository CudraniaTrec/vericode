method LongestCommonSubsequence3(s1: seq<char>, s2: seq<char>, s3: seq<char>) returns (lcs: seq<char>)
{
    var n := |s1|;
    var m := |s2|;
    var p := |s3|;

    var dp := new int[n + 1, m + 1, p + 1];

    // Fill DP table
    var i: int := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall ii :: 0 <= ii < i ==>
            forall jj, kk :: 0 <= jj <= m && 0 <= kk <= p ==>
                0 <= dp[ii, jj, kk] <= ii
    {
        var j: int := 0;
        while j <= m
            invariant 0 <= j <= m + 1
            invariant forall jj :: 0 <= jj < j ==>
                forall ii, kk :: 0 <= ii <= i && 0 <= kk <= p ==>
                    0 <= dp[ii, jj, kk] <= ii
        {
            var k: int := 0;
            while k <= p
                invariant 0 <= k <= p + 1
                invariant forall kk :: 0 <= kk < k ==>
                    forall ii, jj :: 0 <= ii <= i && 0 <= jj <= j ==>
                        0 <= dp[ii, jj, kk] <= ii
            {
                if i == 0 || j == 0 || k == 0 {
                    dp[i, j, k] := 0;
                } else if s1[i-1] == s2[j-1] && s2[j-1] == s3[k-1] {
                    dp[i, j, k] := dp[i-1, j-1, k-1] + 1;
                } else {
                    dp[i, j, k] := if dp[i-1, j, k] > dp[i, j-1, k] then
                                       if dp[i-1, j, k] > dp[i, j, k-1] then dp[i-1, j, k] else dp[i, j, k-1]
                                   else
                                       if dp[i, j-1, k] > dp[i, j, k-1] then dp[i, j-1, k] else dp[i, j, k-1];
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Backtrack to recover the sequence
    var res := [];
    var i2 := n;
    var j2 := m;
    var k2 := p;
    while i2 > 0 && j2 > 0 && k2 > 0
        decreases i2 + j2 + k2
    {
        if s1[i2 - 1] == s2[j2 - 1] && s2[j2 - 1] == s3[k2 - 1] {
            res := [s1[i2 - 1]] + res;
            i2 := i2 - 1;
            j2 := j2 - 1;
            k2 := k2 - 1;
        } else if dp[i2-1, j2, k2] >= dp[i2, j2-1, k2] && dp[i2-1, j2, k2] >= dp[i2, j2, k2-1] {
            i2 := i2 - 1;
        } else if dp[i2, j2-1, k2] >= dp[i2-1, j2, k2] && dp[i2, j2-1, k2] >= dp[i2, j2, k2-1] {
            j2 := j2 - 1;
        } else {
            k2 := k2 - 1;
        }
    }
    lcs := res;
}