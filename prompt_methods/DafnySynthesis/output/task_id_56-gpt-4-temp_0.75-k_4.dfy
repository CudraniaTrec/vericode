method IsOneLessThanTwiceReverse(n: int) returns (res: bool)
{
    // Helper function to reverse the digits of a non-negative integer
    function Reverse(x: int): int
        requires x >= 0
    {
        if x < 10 then x
        else (x % 10) * 10^(NumDigits(x) - 1) + Reverse(x / 10)
    }

    // Helper function to count number of digits in a non-negative integer
    function NumDigits(x: int): int
        requires x >= 0
    {
        if x < 10 then 1
        else 1 + NumDigits(x / 10)
    }

    if n < 0 then
        res := false;
    else
        var rev := Reverse(n);
        res := n == 2 * rev - 1;
}