method MinDifference(arr: array<int>) returns (minDiff: int)
    requires arr != null && arr.Length >= 2
    ensures 0 <= minDiff
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> minDiff <= if arr[i] > arr[j] then arr[i] - arr[j] else arr[j] - arr[i]
{
    // Copy elements to a sequence for sorting
    var seq := [arr[i] | i := 0 .. arr.Length];

    // Sort the sequence
    var sorted := seq[..];
    sorted := sorted[:];
    // Simple insertion sort for demonstration
    var n := |sorted|;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 0 <= k < i-1 ==> sorted[k] <= sorted[k+1]
        decreases n - i
    {
        var j := i;
        while j > 0 && sorted[j] < sorted[j-1]
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < i ==> sorted[k] <= sorted[k+1] || k+1 == j
            decreases j
        {
            var tmp := sorted[j];
            sorted[j] := sorted[j-1];
            sorted[j-1] := tmp;
            j := j - 1;
        }
        i := i + 1;
    }

    // Now find minimal difference between adjacent elements
    minDiff := sorted[1] - sorted[0];
    i := 1;
    while i < n
        invariant 1 <= i < n+1
        invariant 0 <= minDiff
        invariant forall k :: 1 <= k < i ==> minDiff <= sorted[k] - sorted[k-1]
        decreases n - i
    {
        var diff := sorted[i] - sorted[i-1];
        if diff < minDiff {
            minDiff := diff;
        }
        i := i + 1;
    }
}