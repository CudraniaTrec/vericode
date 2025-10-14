// Dafny Code

method PerfectSquaresInRange(a: int, b: int) returns (squares: seq<int>)
    requires a <= b
    ensures forall x :: 0 <= x < |squares| ==> a <= squares[x] <= b
    ensures forall x :: a <= x <= b && exists y :: y * y == x ==> x in squares
{
    var first := if a <= 0 then 0 else (if sqrt(a) * sqrt(a) < a then sqrt(a) + 1 else sqrt(a));
    var last := sqrt(b);
    var result := new seq<int>[];
    var i := first;
    while i <= last
        invariant i >= first && i <= last + 1
        invariant result == [j * j | j := first .. i - 1]
    {
        var sq := i * i;
        if sq >= a && sq <= b {
            result := result + [sq];
        }
        i := i + 1;
    }
    squares := result;
}

// Helper: integer square root (floor)
function method sqrt(n: int): int
    requires n >= 0
    ensures result * result <= n < (result + 1) * (result + 1)
{
    if n < 2 then n
    else
        var lo := 1;
        var hi := n;
        while lo < hi
            invariant 1 <= lo <= hi <= n
            invariant lo * lo <= n
        {
            var mid := lo + (hi - lo) / 2;
            if mid * mid > n {
                hi := mid;
            } else {
                if (mid + 1) * (mid + 1) > n {
                    return mid;
                }
                lo := mid + 1;
            }
        }
        lo
}