
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
    // Invariant: res contains only elements from a[0..i) that are not in b, and all are unique
    // Invariant: forall x :: x in res ==> (exists k :: 0 <= k < i && a[k] == x && !InArray(b, x))
    // Invariant: forall k :: 0 <= k < i :: (a[k] !in res) || (!InArray(b, a[k]))
    // Invariant: forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res ==> (exists k :: 0 <= k < i && a[k] == x && !InArray(b, x))
        invariant forall k :: 0 <= k < i ==> (a[k] !in res) || (!InArray(b, a[k]))
        invariant forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
    {
        if !InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
            assert InArray(a, a[i]) && !InArray(b, a[i]);
        }
    }

    ghost var partialSize := |res|;
    // Invariant: 
    //   - res[0..partialSize) contains all a[0..a.Length) not in b, unique
    //   - res[partialSize..|res|) contains b[0..i) not in a, unique, and not in res[0..partialSize)
    //   - all elements are unique
    //   - for all k < i, b[k] in res[partialSize..|res|) or InArray(a, b[k])
    for i := 0 to b.Length
        invariant 0 <= i <= b.Length
        invariant partialSize == |res| - (|res| - partialSize)
        invariant forall x :: x in res[..partialSize] ==> (InArray(a, x) && !InArray(b, x))
        invariant forall x :: x in res[partialSize..] ==> (!InArray(a, x) && InArray(b, x))
        invariant forall i1, j1 :: 0 <= i1 < j1 < |res| ==> res[i1] != res[j1]
        invariant forall k :: 0 <= k < i ==> (b[k] !in res) || InArray(a, b[k])
    {
        if !InArray(a, b[i]) && b[i] !in res
        {
            res := res + [b[i]];
            assert !InArray(a, b[i]) && InArray(b, b[i]);
        }
    }

    result := res;
}

function abs(a: real) : real {if a>0.0 then a else -a}
