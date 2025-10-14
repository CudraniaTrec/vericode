
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{
    result := [];
    // Outer loop invariant
    var n := |a|;
    for i := 0 to |a|
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
    {
        var subResult := [];
        var m := |a[i]|;
        // Inner loop invariant
        for j := 0 to |a[i]|
            invariant 0 <= j <= m
            invariant |subResult| == j
            invariant forall l :: 0 <= l < j ==> subResult[l] == a[i][l] + b[i][l]
        {
            subResult := subResult + [a[i][j] + b[i][j]];
            assert subResult[j] == a[i][j] + b[i][j];
        }
        assert |subResult| == |a[i]|;
        assert forall j :: 0 <= j < |subResult| ==> subResult[j] == a[i][j] + b[i][j];
        result := result + [subResult];
        assert |result| == i + 1;
        assert |result[i]| == |a[i]|;
        assert forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j];
    }
    assert |result| == |a|;
    assert forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|;
    assert forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
