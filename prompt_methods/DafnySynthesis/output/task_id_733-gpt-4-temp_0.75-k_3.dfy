method FirstOccurrence(a: array<int>, key: int) returns (idx: int)
    requires a != null
    ensures 0 <= idx <= a.Length
    ensures idx < a.Length ==> a[idx] == key
    ensures idx == a.Length || (idx > 0 ==> a[idx - 1] < key)
    ensures forall j :: 0 <= j < idx ==> a[j] < key
{
    var low := 0;
    var high := a.Length;
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall j :: 0 <= j < low ==> a[j] < key
        invariant forall j :: high <= j < a.Length ==> a[j] >= key
    {
        var mid := low + (high - low) / 2;
        if a[mid] < key {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    idx := low;
}