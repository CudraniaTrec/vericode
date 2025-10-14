method HighestPowerOf2LE(n: nat) returns (result: nat)
    ensures result <= n
    ensures result > 0 ==> result <= n
    ensures result > 0 ==> result * 2 > n
    ensures result == 0 <==> n == 0
{
    if n == 0 {
        return 0;
    }
    var res := 1;
    while res * 2 <= n
        invariant 1 <= res <= n
        invariant res & (res - 1) == 0 // res is a power of 2
        decreases n - res
    {
        res := res * 2;
    }
    return res;
}