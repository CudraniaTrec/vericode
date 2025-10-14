
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
        invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    {
        if a[i] !in res
        {
            assert forall j :: 0 <= j < |res| ==> res[j] != a[i];
            res := res + [a[i]];
        }
        i := i + 1;
    }
    result := res;
}

function abs(a: real) : real {if a>0.0 then a else -a}
