
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{
    diff := [];
    var i: int := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in diff <==> (x in a[..i] && x !in b)
        invariant forall m, n :: 0 <= m < n < |diff| ==> diff[m] != diff[n]
        invariant forall x :: x in diff ==> x !in b
        invariant |diff| <= i
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
