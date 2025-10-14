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
    // Invariant: res contains only elements from a[0..i) not in b and not repeated
    // Invariant: all elements in res are unique
    // Invariant: forall x :: x in res ==> (InArray(a, x) && !InArray(b, x))
    // Invariant: forall i1, i2 :: 0 <= i1 < i2 < |res| ==> res[i1] != res[i2]
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res ==> (InArray(a, x) && !InArray(b, x))
        invariant forall i1, i2 :: 0 <= i1 < i2 < |res| ==> res[i1] != res[i2]
    {
        if !InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
        }
    }

    ghost var partialSize := |res|;
    // Invariant: res contains all elements from a[0..a.Length) not in b, and now adding from b[0..i) not in a and not repeated
    // Invariant: all elements in res are unique
    // Invariant: forall x :: x in res[..partialSize] ==> (InArray(a, x) && !InArray(b, x))
    // Invariant: forall x :: x in res[partialSize..] ==> (!InArray(a, x) && InArray(b, x))
    // Invariant: forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
    // Invariant: forall i1, i2 :: 0 <= i1 < i2 < |res| ==> res[i1] != res[i2]
    for i := 0 to b.Length
        invariant 0 <= i <= b.Length
        invariant |res| >= partialSize
        invariant forall x :: x in res[..partialSize] ==> (InArray(a, x) && !InArray(b, x))
        invariant forall x :: x in res[partialSize..] ==> (!InArray(a, x) && InArray(b, x))
        invariant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
        invariant forall i1, i2 :: 0 <= i1 < i2 < |res| ==> res[i1] != res[i2]
    {
        if !InArray(a, b[i]) && b[i] !in res
        {
            res := res + [b[i]];
        }
    }

    result := res;
}

function abs(a: real) : real {if a>0.0 then a else -a}
