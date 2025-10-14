//Dafny Code

method FirstOccurrenceIndex(a: array<int>, key: int) returns (idx: int)
    requires a != null
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // a is sorted non-decreasingly
    ensures -1 <= idx < a.Length
    ensures idx == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
    ensures 0 <= idx < a.Length ==> a[idx] == key
    ensures 0 <= idx < a.Length ==> idx == 0 || a[idx - 1] < key
{
    var low := 0;
    var high := a.Length - 1;
    var res := -1;
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= res < a.Length
        invariant high < a.Length
        invariant forall k :: 0 <= k < low ==> a[k] < key || (res != -1 && k >= res)
        invariant forall k :: high < k < a.Length ==> a[k] >= key
    {
        var mid := low + (high - low) / 2;
        if a[mid] == key {
            res := mid;
            high := mid - 1;
        } else if a[mid] < key {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    idx := res;
}