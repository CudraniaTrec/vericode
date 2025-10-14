
method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
    {
        assert 0 <= i < |a| ==> b[i] != 0;
        result := result + [a[i] / b[i]];
        i := i + 1;
    }
    assert |result| == |a|;
    assert forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
