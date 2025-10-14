method bellNumber(n:int) returns (res:int)
    requires n >= 0
{
    // Bell numbers using dynamic programming (Bell triangle)
    if n == 0 {
        res := 1;
        return;
    }
    var bell := new int[n+1][n+1];
    bell[0][0] := 1;
    var i, j: int;
    for i := 1 to n {
        bell[i][0] := bell[i-1][i-1];
        for j := 1 to i {
            bell[i][j] := bell[i][j-1] + bell[i-1][j-1];
        }
    }
    res := bell[n][0];
}