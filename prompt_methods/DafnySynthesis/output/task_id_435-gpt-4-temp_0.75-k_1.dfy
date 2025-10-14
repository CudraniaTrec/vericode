method LastDigit(n: int) returns (d: int)
    ensures 0 <= d < 10
    ensures n >= 0 ==> d == n % 10
    ensures n < 0 ==> d == (-n) % 10
{
    if n >= 0 {
        d := n % 10;
    } else {
        d := (-n) % 10;
    }
}