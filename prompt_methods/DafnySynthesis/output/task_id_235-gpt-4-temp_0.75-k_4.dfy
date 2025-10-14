method SetAllEvenBits(n: int) returns (result: int)
    ensures result == n | EvenBitsMask()
{
    result := n | EvenBitsMask();
}

/// Returns a mask with all even bits set for a 32-bit integer.
/// That is, bits 0, 2, 4, ..., 30 are 1, others 0.
function EvenBitsMask(): int
{
    0x55555555 // binary: 01010101...01 (32 bits)
}