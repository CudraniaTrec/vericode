method SumOfMinAndMax(a: array<int>) returns (sum: int)
    requires a != null && a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] >= min(a) && a[i] <= max(a)
    ensures sum == min(a) + max(a)
{
    var min := a[0];
    var max := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> min <= a[j] <= max
        invariant min == (if forall j :: 0 <= j < i ==> a[j] >= min then min else min(a[..i]))
        invariant max == (if forall j :: 0 <= j < i ==> a[j] <= max then max else max(a[..i]))
    {
        if a[i] < min {
            min := a[i];
        }
        if a[i] > max {
            max := a[i];
        }
        i := i + 1;
    }
    sum := min + max;
}

// Helper functions for specifications
function min(a: seq<int>): int
    requires |a| > 0
{
    if |a| == 1 then a[0] else if a[0] < min(a[1..]) then a[0] else min(a[1..])
}

function max(a: seq<int>): int
    requires |a| > 0
{
    if |a| == 1 then a[0] else if a[0] > max(a[1..]) then a[0] else max(a[1..])
}