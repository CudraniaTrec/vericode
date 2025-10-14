method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
    var rotated: seq<int> := [];
    var len := |l|;
    // Invariant: rotated contains the first i rotated elements
    for i := 0 to len
        invariant 0 <= i <= len
        invariant |rotated| == i
        invariant forall j :: 0 <= j < i ==> rotated[j] == l[(j - n + len) % len]
    {
        rotated := rotated + [l[(i - n + len) % len]];
        assert |rotated| == i + 1;
        assert rotated[i] == l[(i - n + len) % len];
    }
    r := rotated;
    assert |r| == |l|;
    assert forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|];
    return r;
}
function abs(a: real) : real {if a>0.0 then a else -a}
