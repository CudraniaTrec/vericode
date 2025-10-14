method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
{
    result := false;
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k: int, l: int :: 0 <= k < i && 0 <= l < b.Length ==> a[k] != b[l]
        decreases a.Length - i
    {
        var j: int := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant forall l: int :: 0 <= l < j ==> a[i] != b[l]
            decreases b.Length - j
        {
            if a[i] == b[j] {
                result := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}