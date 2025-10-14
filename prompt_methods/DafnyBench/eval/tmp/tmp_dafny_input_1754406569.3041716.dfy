method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{
    // arr[..L] gives the first L elements, arr[L..] gives the rest
    // Let's assert these facts for clarity
    assert arr[..L] + arr[L..] == arr[..];
    assert |arr[..L]| == L;
    assert |arr[L..]| == arr.Length - L;
    firstPart := arr[..L];
    secondPart := arr[L..];
    assert |firstPart| == L;
    assert |secondPart| == arr.Length - L;
    assert firstPart + secondPart == arr[..];
}
function abs(a: real) : real {if a>0.0 then a else -a}
