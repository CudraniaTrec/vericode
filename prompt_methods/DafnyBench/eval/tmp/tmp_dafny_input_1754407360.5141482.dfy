
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{
    diff := [];
    var i: int := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in diff <==> (exists k :: 0 <= k < i && a[k] == x && a[k] !in b)
        invariant forall p, q :: 0 <= p < q < |diff| ==> diff[p] != diff[q]
    {
        if a[i] !in b && a[i] !in diff
        {
            diff := diff + [a[i]];
            assert a[i] !in b;
            assert a[i] !in diff[..|diff|-1];
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
