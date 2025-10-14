// Dafny Code

method CountEqual(a: int, b: int, c: int) returns (count: int)
{
    if a == b && b == c {
        count := 3;
    } else if a == b || a == c || b == c {
        count := 2;
    } else {
        count := 0;
    }
}