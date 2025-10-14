//Dafny Code

method PerfectSquaresInRange(a: int, b: int) returns (squares: seq<int>)
    requires a <= b
    ensures forall x :: 0 <= x < |squares| ==> squares[x] * squares[x] >= a && squares[x] * squares[x] <= b
    ensures forall n :: a <= n <= b && exists k :: k * k == n ==> n in squares[*] * squares[*]
    decreases b - a
{
    var result := [];
    var start := if a <= 0 then 0 else if sqrt(a) * sqrt(a) < a then sqrt(a) + 1 else sqrt(a);
    var end_ := sqrt(b);
    var k := start;
    while k <= end_
        invariant k >= start
        invariant k <= end_ + 1
        invariant result == [i | i := start .. k-1]
    {
        result := result + [k];
        k := k + 1;
    }
    squares := result;
}

// Helper function for integer square root
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
            var mid := (lo + hi + 1) / 2;
            if mid * mid <= n {
                lo := mid;
            } else {
                hi := mid - 1;
            }
        }
        lo
}