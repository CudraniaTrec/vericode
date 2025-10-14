method SecondSmallest(a: array<int>) returns (secondMin: int)
    requires a != null && a.Length >= 2
    ensures exists i, j :: 0 <= i < j < a.Length && (a[i] == secondMin || a[j] == secondMin)
{
    var min := if a[0] < a[1] then a[0] else a[1];
    var sec := if a[0] < a[1] then a[1] else a[0];

    var i := 2;
    while i < a.Length
        invariant 2 <= i <= a.Length
        invariant min <= sec
        invariant forall k :: 0 <= k < i ==> a[k] >= min
        invariant forall k :: 0 <= k < i ==> a[k] == min || a[k] >= sec
    {
        if a[i] < min {
            sec := min;
            min := a[i];
        } else if a[i] < sec && a[i] != min {
            sec := a[i];
        }
        i := i + 1;
    }
    secondMin := sec;
}