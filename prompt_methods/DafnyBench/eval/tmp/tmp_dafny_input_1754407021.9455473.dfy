
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    // Invariant: res contains only elements from a that are not in b, and all are unique
    // Invariant: forall x :: x in res ==> (InArray(a, x) && !InArray(b, x))
    // Invariant: forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    // Invariant: forall k :: 0 <= k < i ==> a[k] in res || InArray(b, a[k])
    // Invariant: forall x :: x in res ==> exists k :: 0 <= k < i && a[k] == x
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res ==> (InArray(a, x) && !InArray(b, x))
        invariant forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
        invariant forall k :: 0 <= k < i ==> a[k] in res || InArray(b, a[k])
        invariant forall x :: x in res ==> exists k :: 0 <= k < i && a[k] == x
    {
        if !InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
            assert InArray(a, a[i]) && !InArray(b, a[i]);
            assert a[i] !in res[..|res|-1];
        }
    }

    ghost var partialSize := |res|;
    // Invariant: res contains all elements from a not in b, and all unique, and possibly some from b not in a
    // Invariant: forall x :: x in res[..partialSize] ==> (InArray(a, x) && !InArray(b, x))
    // Invariant: forall x :: x in res[partialSize..] ==> (!InArray(a, x) && InArray(b, x))
    // Invariant: forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
    // Invariant: |res[..partialSize]| == partialSize
    // Invariant: forall k :: 0 <= k < i ==> b[k] in res[partialSize..] || InArray(a, b[k])
    // Invariant: forall x :: x in res[partialSize..] ==> exists k :: 0 <= k < i && b[k] == x
    for i := 0 to b.Length
        invariant 0 <= i <= b.Length
        invariant |res[..partialSize]| == partialSize
        invariant forall x :: x in res[..partialSize] ==> (InArray(a, x) && !InArray(b, x))
        invariant forall x :: x in res[partialSize..] ==> (!InArray(a, x) && InArray(b, x))
        invariant forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
        invariant forall k :: 0 <= k < i ==> b[k] in res[partialSize..] || InArray(a, b[k])
        invariant forall x :: x in res[partialSize..] ==> exists k :: 0 <= k < i && b[k] == x
    {
        if !InArray(a, b[i]) && b[i] !in res
        {
            res := res + [b[i]];
            assert !InArray(a, b[i]) && InArray(b, b[i]);
            assert b[i] !in res[..|res|-1];
        }
    }

    result := res;
}

function abs(a: real) : real {if a>0.0 then a else -a}
