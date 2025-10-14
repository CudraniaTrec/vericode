
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res ==> InArray(a, x) && !InArray(b, x)
        invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
        invariant forall j :: 0 <= j < i ==> a[j] in res || InArray(b, a[j]) || (exists k :: 0 <= k < j && a[j] == a[k])
        decreases a.Length - i
    {
        if !InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
            assert InArray(a, a[i]);
            assert !InArray(b, a[i]);
            assert a[i] !in res[..|res|-1];
        }
        i := i + 1;
    }

    result := res;
}

function abs(a: real) : real {if a>0.0 then a else -a}
