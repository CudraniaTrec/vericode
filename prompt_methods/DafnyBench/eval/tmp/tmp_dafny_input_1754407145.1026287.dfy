method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{
    result := [];
    var n := |a|;
    // Invariant: result contains the element-wise division of the first i elements
    // Invariant: |result| == i
    // Invariant: forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
    // Invariant: 0 <= i <= n
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] / b[j]
    {
        assert i < n ==> b[i] != 0;
        if i < n {
            result := result + [a[i] / b[i]];
        }
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
