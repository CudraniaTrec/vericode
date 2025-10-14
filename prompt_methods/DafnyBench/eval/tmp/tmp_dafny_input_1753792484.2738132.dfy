
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res <==> exists j :: 0 <= j < i && a[j] == x
        invariant forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2]
    {
        if a[i] !in res
        {
            res := res + [a[i]];
            assert a[i] !in res[..|res|-1];
            assert forall k :: 0 <= k < |res|-1 ==> res[k] != res[|res|-1];
        }
        i := i + 1;
    }
    result := res;
    assert forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x;
    assert forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
