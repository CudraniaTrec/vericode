
method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
    s := [];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant |s| == i
        invariant forall j :: 0 <= j < i ==> s[j] == a[j]
    {
        s := s + [a[i]];
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
