method SumOfDigits(n: nat) returns (sum: nat)
    ensures sum == (if n == 0 then 0 else sum i | i := n; i > 0; i := i / 10 :: i % 10)
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant 0 <= temp <= n
        invariant sum + (if temp == 0 then 0 else sum i | i := temp; i > 0; i := i / 10 :: i % 10) == (if n == 0 then 0 else sum i | i := n; i > 0; i := i / 10 :: i % 10)
    {
        sum := sum + temp % 10;
        temp := temp / 10;
    }
}