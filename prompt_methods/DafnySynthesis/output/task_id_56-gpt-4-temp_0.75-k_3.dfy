method IsOneLessThanTwiceReverse(n: int) returns (res: bool)
    ensures res == (n == 2 * Reverse(n) - 1)
{
    // Helper function to reverse the digits of n
    function Reverse(x: int): int
        requires x >= 0
    {
        if x < 10 then x
        else
            var s := x.ToString();
            var rev := s[..][|s.Length-1,0,-1|].Concat();
            rev as int
    }

    if n < 0 {
        res := false;
        return;
    }
    res := n == 2 * Reverse(n) - 1;
}