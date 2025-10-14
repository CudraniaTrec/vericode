method SmallestPowerOf2GE(n: nat) returns (res: nat)
    ensures res >= n
    ensures res > 0
    ensures res as int == 1 << (if n == 0 then 0 else |n - 1|.DigitsInBase(2))
    ensures res == 1 || (res / 2 < n <= res)
{
    if n == 0 {
        res := 1;
        return;
    }
    var x := n - 1;
    var k := 1;
    while k < 32 // assuming 32-bit numbers; adjust as needed
        invariant k >= 1 && k <= 32
        invariant x + 1 >= n
        decreases 32 - k
    {
        x := x | (x >> k);
        k := k * 2;
    }
    res := x + 1;
}