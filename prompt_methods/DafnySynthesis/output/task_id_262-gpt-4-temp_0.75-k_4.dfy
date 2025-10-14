method SplitArray<T>(a: array<T>, L: int) returns (res: seq<seq<T>>)
    requires 0 <= L <= a.Length
    ensures res.Length == 2
    ensures res[0] == a[0 .. L]
    ensures res[1] == a[L .. a.Length]
{
    var firstPart := a[0 .. L];
    var secondPart := a[L .. a.Length];
    res := [firstPart, secondPart];
}