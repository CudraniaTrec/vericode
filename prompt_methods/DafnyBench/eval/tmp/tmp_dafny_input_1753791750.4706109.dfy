
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
    var identical := set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i];
    assert forall i :: 0 <= i < |a| ==> (i in identical) == (a[i] == b[i] && b[i] == c[i]);
    assert identical <= set i: int | 0 <= i < |a|;
    assert forall i :: i in identical ==> 0 <= i < |a|;
    count := |identical|;
    assert count >= 0;
    assert count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
