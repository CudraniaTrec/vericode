method LastPositionOf(a: array<int>, key: int) returns (idx: int)
    requires a != null
    requires a.Length >= 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // sorted non-decreasing
    ensures -1 <= idx < a.Length
    ensures idx == -1 || a[idx] == key
    ensures idx == -1 || (idx == a.Length - 1 || a[idx + 1] > key)
{
    var lo := 0;
    var hi := a.Length - 1;
    idx := -1;
    while lo <= hi
        invariant 0 <= lo <= a.Length
        invariant -1 <= idx < a.Length
        invariant hi < a.Length
        invariant forall k :: 0 <= k < lo ==> a[k] <= key ==> idx >= k ==> (idx == -1 || a[idx] == key)
        invariant forall k :: hi < k < a.Length ==> a[k] > key
        invariant forall k :: idx < k < a.Length ==> a[k] > key
    {
        var mid := lo + (hi - lo) / 2;
        if a[mid] == key {
            idx := mid;
            lo := mid + 1; // look for later occurrence
        } else if a[mid] < key {
            lo := mid + 1;
        } else {
            hi := mid - 1;
        }
    }
}