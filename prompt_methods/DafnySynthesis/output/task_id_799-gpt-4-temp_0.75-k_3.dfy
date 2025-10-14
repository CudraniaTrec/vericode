// Dafny Code

method RotateLeft32(x: uint, d: uint) returns (res: uint)
    requires d < 32  // Only meaningful to rotate by < 32 bits
    ensures res == ((x << d) | (x >> (32 - d))) % (1 << 32)
{
    // Since Dafny's << and >> on uint already wrap modulo 32 bits,
    // but we use % (1 << 32) to ensure the result is in 32 bits.
    var left := x << d;
    var right := x >> (32 - d);
    res := (left | right) % (1 << 32);
}