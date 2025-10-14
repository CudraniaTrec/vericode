method LongestCommonSubsequence3(s1: seq<char>, s2: seq<char>, s3: seq<char>) returns (lcs: seq<char>)
{
    var n := |s1|;
    var m := |s2|;
    var o := |s3|;

    // Create a 3D array for DP
    var dp := new int[n+1, m+1, o+1];
    // For reconstruction
    var dir := new int[n+1, m+1, o+1]; // 0:diag, 1:i-1, 2:j-1, 3:k-1

    // Fill dp table
    var i: int := 0;
    while i <= n
        invariant 0 <= i <= n+1
        decreases n - i + 1
    {
        var j: int := 0;
        while j <= m
            invariant 0 <= j <= m+1
            decreases m - j + 1
        {
            var k: int := 0;
            while k <= o
                invariant 0 <= k <= o+1
                decreases o - k + 1
            {
                if i == 0 || j == 0 || k == 0 {
                    dp[i, j, k] := 0;
                    dir[i, j, k] := -1;
                } else if s1[i-1] == s2[j-1] && s2[j-1] == s3[k-1] {
                    dp[i, j, k] := dp[i-1, j-1, k-1] + 1;
                    dir[i, j, k] := 0;
                } else {
                    if dp[i-1, j, k] >= dp[i, j-1, k] && dp[i-1, j, k] >= dp[i, j, k-1] {
                        dp[i, j, k] := dp[i-1, j, k];
                        dir[i, j, k] := 1;
                    } else if dp[i, j-1, k] >= dp[i-1, j, k] && dp[i, j-1, k] >= dp[i, j, k-1] {
                        dp[i, j, k] := dp[i, j-1, k];
                        dir[i, j, k] := 2;
                    } else {
                        dp[i, j, k] := dp[i, j, k-1];
                        dir[i, j, k] := 3;
                    }
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Reconstruct the LCS
    var res := new seq<char>[];
    var x := n;
    var y := m;
    var z := o;
    while x > 0 && y > 0 && z > 0
        invariant 0 <= x <= n
        invariant 0 <= y <= m
        invariant 0 <= z <= o
        decreases x + y + z
    {
        if dir[x, y, z] == 0 {
            res := [s1[x-1]] + res;
            x := x - 1;
            y := y - 1;
            z := z - 1;
        } else if dir[x, y, z] == 1 {
            x := x - 1;
        } else if dir[x, y, z] == 2 {
            y := y - 1;
        } else if dir[x, y, z] == 3 {
            z := z - 1;
        } else {
            // Done
            break;
        }
    }
    lcs := res;
}