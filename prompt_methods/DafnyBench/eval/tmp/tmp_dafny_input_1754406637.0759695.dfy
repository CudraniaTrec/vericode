
method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
{
    var newSeq: seq<int> := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |newSeq| == i
        invariant forall j :: 0 <= j < i ==> newSeq[j] == s[j]
    {
        newSeq := newSeq + [s[i]];
        i := i + 1;
    }
    copy := newSeq;
}

function abs(a: real) : real {if a>0.0 then a else -a}
