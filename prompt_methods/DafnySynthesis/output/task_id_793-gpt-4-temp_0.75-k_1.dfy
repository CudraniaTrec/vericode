method LastPositionOf(a: array<int>, x: int) returns (idx: int)
    requires a != null
    requires a.Length >= 0
    requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // sorted non-decreasing
    ensures -1 <= idx < a.Length
    ensures idx == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
    ensures idx != -1 ==> a[idx] == x && (idx == a.Length-1 || a[idx+1] != x)
{
    var lo := 0;
    var hi := a.Length - 1;
    idx := -1;
    while lo <= hi
        invariant 0 <= lo <= a.Length
        invariant -1 <= hi < a.Length
        invariant idx == -1 || (0 <= idx < a.Length && a[idx] == x)
        invariant forall i :: 0 <= i < lo ==> a[i] <= x
        invariant forall i :: hi+1 <= i < a.Length ==> a[i] > x
        decreases hi - lo + 1
    {
        var mid := lo + (hi - lo) / 2;
        if a[mid] == x {
            idx := mid;
            lo := mid + 1; // search to the right for later occurrence
        } else if a[mid] < x {
            lo := mid + 1;
        } else {
            hi := mid - 1;
        }
    }
}