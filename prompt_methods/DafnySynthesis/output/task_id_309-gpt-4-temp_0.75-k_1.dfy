method Max(a: int, b: int) returns (max: int)
    ensures max == if a >= b then a else b
{
    if a >= b {
        max := a;
    } else {
        max := b;
    }
}