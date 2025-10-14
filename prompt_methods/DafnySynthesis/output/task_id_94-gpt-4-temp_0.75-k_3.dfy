method FirstValueWithSmallestSecondValue(a: array<seq<int>>) returns (firstValue: int)
    requires a != null && a.Length > 0
    requires forall i :: 0 <= i < a.Length ==> |a[i]| >= 2
    ensures exists i :: 0 <= i < a.Length && firstValue == a[i][0]
    ensures forall i :: 0 <= i < a.Length ==> a[i][1] >= (a[j][1] | exists j :: 0 <= j < a.Length && firstValue == a[j][0])
{
    var minIdx := 0;
    var minSecond := a[0][1];
    var minFirst := a[0][0];

    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant 0 <= minIdx < a.Length
        invariant minSecond == a[minIdx][1]
        invariant minFirst == a[minIdx][0]
        invariant forall j :: 0 <= j < i ==> a[j][1] >= minSecond
    {
        if a[i][1] < minSecond {
            minIdx := i;
            minSecond := a[i][1];
            minFirst := a[i][0];
        }
        i := i + 1;
    }
    firstValue := minFirst;
}