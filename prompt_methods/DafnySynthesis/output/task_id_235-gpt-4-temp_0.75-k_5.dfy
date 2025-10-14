method SetAllEvenBits(n: int) returns (result: int)
    requires n >= 0
    ensures result == n | EvenBitsMask(n)
{
    var mask := EvenBitsMask(n);
    result := n | mask;
}

/// Helper function to create a mask with all even bits set up to the highest bit in n
function EvenBitsMask(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else
        var numBits := 0;
        var temp := n;
        while temp > 0
            decreases temp
        {
            temp := temp / 2;
            numBits := numBits + 1;
        }
        var mask := 0;
        var i := 0;
        while i < numBits
            decreases numBits - i
        {
            if i % 2 == 0 {
                mask := mask | (1 << i);
            }
            i := i + 1;
        }
        mask
}