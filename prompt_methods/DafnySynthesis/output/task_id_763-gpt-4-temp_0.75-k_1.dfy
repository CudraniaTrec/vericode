method MinDifference(a: array<int>) returns (minDiff: int)
    requires a != null && a.Length >= 2
    ensures minDiff >= 0
    ensures forall i, j :: 0 <= i < j < a.Length ==> minDiff <= if a[i] > a[j] then a[i] - a[j] else a[j] - a[i]
{
    // First, make a local copy of the array and sort it
    var n := a.Length;
    var b := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    {
        b[i] := a[i];
        i := i + 1;
    }
    // Simple insertion sort
    var j := 1;
    while j < n
        invariant 1 <= j <= n
        invariant multiset(b[..j]) == multiset(a[..j])
        invariant forall k :: 1 <= k < j ==> b[k-1] <= b[k]
    {
        var x := b[j];
        var k := j;
        while k > 0 && b[k-1] > x
            invariant 0 <= k <= j
            invariant b[k..j] == b[(k-1)..(j-1)]
            invariant forall m :: 1 <= m < k ==> b[m-1] <= b[m]
        {
            b[k] := b[k-1];
            k := k - 1;
        }
        b[k] := x;
        j := j + 1;
    }
    // Now, find minimum difference between consecutive elements
    minDiff := b[1] - b[0];
    var m := 2;
    while m < n
        invariant 2 <= m <= n
        invariant minDiff >= 0
        invariant forall t :: 1 <= t < m ==> minDiff <= b[t] - b[t-1]
    {
        var diff := b[m] - b[m-1];
        if diff < minDiff {
            minDiff := diff;
        }
        m := m + 1;
    }
}