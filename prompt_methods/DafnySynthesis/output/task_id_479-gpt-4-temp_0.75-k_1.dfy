method FirstDigit(n: int) returns (digit: int)
    requires n > 0
    ensures 1 <= digit <= 9
    ensures forall k :: n == k * 10 + digit ==> k == 0 ==> true
{
    var m := n;
    while m >= 10
        invariant m > 0
        invariant m <= n
    {
        m := m / 10;
    }
    digit := m;
}