method Min(a: int, b: int) returns (min: int)
    ensures min == if a < b then a else b
{
    if a < b {
        min := a;
    } else {
        min := b;
    }
}