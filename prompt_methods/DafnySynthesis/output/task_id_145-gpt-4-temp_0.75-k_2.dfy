method MaxDifference(a: array<int>) returns (maxDiff: int)
    requires a != null && a.Length > 1
    ensures maxDiff == (max a[i] | 0 <= i < a.Length) - (min a[i] | 0 <= i < a.Length)
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == (min a[j] | 0 <= j < i)
        invariant maxVal == (max a[j] | 0 <= j < i)
    {
        if a[i] < minVal {
            minVal := a[i];
        }
        if a[i] > maxVal {
            maxVal := a[i];
        }
        i := i + 1;
    }
    maxDiff := maxVal - minVal;
}