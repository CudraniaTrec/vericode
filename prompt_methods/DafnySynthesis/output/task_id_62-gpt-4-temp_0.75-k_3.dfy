method FindSmallest(a: array<int>) returns (min: int)
    requires a != null && a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> min <= a[i]
    ensures exists i :: 0 <= i < a.Length && min == a[i]
{
    var currentMin := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> currentMin <= a[j]
        invariant exists j :: 0 <= j < i && currentMin == a[j]
    {
        if a[i] < currentMin {
            currentMin := a[i];
        }
        i := i + 1;
    }
    min := currentMin;
}