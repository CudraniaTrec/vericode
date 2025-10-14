method SmallestPowerOf2GE(n: nat) returns (result: nat)
    ensures result >= n
    ensures result > 0
    ensures (result & (result - 1)) == 0 // result is a power of 2
    ensures result/2 < n || n == 0
{
    if n == 0 {
        return 1;
    }
    var x := n - 1;
    var shift := 1;
    while shift < 64 // Assuming 64-bit numbers; adjust if needed
        invariant shift <= 64
        invariant x >= n - 1
        decreases 64 - shift
    {
        x := x | (x >> shift);
        shift := shift * 2;
    }
    return x + 1;
}