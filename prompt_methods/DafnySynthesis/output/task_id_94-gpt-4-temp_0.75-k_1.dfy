method FirstWithSmallestSecond(a: array<seq<int>>) returns (result: int)
    requires a != null && a.Length > 0
    requires forall i :: 0 <= i < a.Length ==> |a[i]| >= 2
    ensures exists i :: 0 <= i < a.Length && result == a[i][0] // result is a first value
    ensures forall i :: 0 <= i < a.Length ==> 
        a[i][1] >= (a[Seq#MinIndex(a, (x: seq<int>) => x[1])][1])
    ensures result == a[Seq#MinIndex(a, (x: seq<int>) => x[1])][0]
{
    var minIndex := 0;
    var minSecond := a[0][1];
    var n := a.Length;
    var i := 1;
    while i < n
        invariant 0 <= minIndex < n
        invariant minSecond == a[minIndex][1]
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i ==> a[j][1] >= minSecond
    {
        if a[i][1] < minSecond {
            minSecond := a[i][1];
            minIndex := i;
        }
        i := i + 1;
    }
    result := a[minIndex][0];
}