
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
    var minVal := a[0];
    var maxVal := a[0];

    // Invariant: minVal and maxVal are the minimum and maximum of a[0..i)
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] <= maxVal
        invariant forall k :: 0 <= k < i ==> minVal <= a[k]
        invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
        invariant minVal == (if i == 1 then a[0] else (min j | 0 <= j < i :: a[j]))
        invariant maxVal == (if i == 1 then a[0] else (max j | 0 <= j < i :: a[j]))
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
        // assert minVal <= maxVal;
    }
    // At this point, minVal and maxVal are the minimum and maximum of a[0..a.Length)
    assert forall k :: 0 <= k < a.Length ==> minVal <= a[k] <= maxVal;
    diff := maxVal - minVal;
    // assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff;
}

function abs(a: real) : real {if a>0.0 then a else -a}
