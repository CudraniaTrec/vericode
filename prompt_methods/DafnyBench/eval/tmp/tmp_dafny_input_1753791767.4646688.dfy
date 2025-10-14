method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
    var minVal := a[0];
    var maxVal := a[0];

    // minVal is the minimum and maxVal is the maximum of a[0..i)
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] <= maxVal
        invariant forall k :: 0 <= k < i ==> minVal <= a[k]
        invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
        invariant exists k :: 0 <= k < i && a[k] == minVal
        invariant exists k :: 0 <= k < i && a[k] == maxVal
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    diff := maxVal - minVal;
}
function abs(a: real) : real {if a>0.0 then a else -a}
