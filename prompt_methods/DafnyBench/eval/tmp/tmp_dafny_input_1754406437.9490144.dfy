
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{
    r := s;
    var n := a.Length;
    // Loop invariant annotations
    var i: int := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |r| == |s| + i
        invariant forall j :: 0 <= j < |s| ==> r[j] == s[j]
        invariant forall j :: 0 <= j < i ==> r[|s| + j] == a[j]
    {
        r := r + [a[i]];
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
