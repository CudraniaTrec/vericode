method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
{
    count := 0;
    var n := |a|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant count == |set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]|
    {
        if a[i] == b[i] && b[i] == c[i] {
            count := count + 1;
        }
        i := i + 1;
    }
    assert count == |set j: int | 0 <= j < n && a[j] == b[j] && b[j] == c[j]|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
