method IsPerfectSquare(n: nat) returns (isSquare: bool)
{
    if n == 0 || n == 1 {
        return true;
    }
    var low := 1;
    var high := n/2;
    while low <= high
        invariant 1 <= low <= n/2 + 1
        invariant high <= n/2
    {
        var mid := (low + high) / 2;
        var sq := mid * mid;
        if sq == n {
            return true;
        } else if sq < n {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    return false;
}