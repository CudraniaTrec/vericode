// Dafny Code

method RotateLeft32(x: uint32, d: nat) returns (res: uint32)
    requires d < 32
{
    // Shift x left by d bits and shift x right by (32 - d) bits,
    // then "or" the results to get the rotated value.
    // Mask with 0xFFFFFFFF to ensure 32-bit result.
    var left := x << d;
    var right := x >> (32 - d);
    res := (left | right) & 0xFFFFFFFFu;
}