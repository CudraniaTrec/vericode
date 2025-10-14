method HighestPowerOf2LE(n: nat) returns (res: nat)
    ensures res <= n && res > 0
    ensures forall k: nat :: k > res ==> k > n || k & (k - 1) != 0
    ensures res & (res - 1) == 0 // res is a power of 2
{
    if n == 0 {
        // No power of 2 less than or equal to 0, but let's define it as 0.
        res := 0;
        return;
    }
    var x := n;
    // Fill all bits to the right with 1s
    x := x | (x >> 1);
    x := x | (x >> 2);
    x := x | (x >> 4);
    x := x | (x >> 8);
    x := x | (x >> 16);
    // x is now a sequence of 1s from the highest set bit down
    res := x - (x >> 1);
}