// Dafny Code

method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures (median == a || median == b || median == c)
    ensures (median == a || median == b) ==> (median <= a && median >= b) || (median >= a && median <= b)
    ensures (median == a || median == c) ==> (median <= a && median >= c) || (median >= a && median <= c)
    ensures (median == b || median == c) ==> (median <= b && median >= c) || (median >= b && median <= c)
{
    if (a >= b) {
        if (b >= c) {
            median := b;
        } else if (a <= c) {
            median := a;
        } else {
            median := c;
        }
    } else {
        if (a >= c) {
            median := a;
        } else if (b <= c) {
            median := b;
        } else {
            median := c;
        }
    }
}