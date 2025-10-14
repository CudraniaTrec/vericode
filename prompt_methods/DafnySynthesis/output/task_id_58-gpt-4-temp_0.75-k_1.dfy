//Dafny Code

method OppositeSign(x: int, y: int) returns (res: bool)
{
    // Two integers have opposite signs if their product is negative,
    // or, equivalently, if one is positive and the other is negative.
    res := (x < 0 && y > 0) || (x > 0 && y < 0);
}