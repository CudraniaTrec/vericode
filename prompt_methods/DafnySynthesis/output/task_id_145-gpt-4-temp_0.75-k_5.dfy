//Dafny Code

method MaxDifference(a: array<int>) returns (maxDiff: int)
    requires a != null && a.Length >= 2
    ensures maxDiff == (max(a[..]) - min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == min(a[..i])
        invariant maxVal == max(a[..i])
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

function method min(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0] else if s[0] < min(s[1..]) then s[0] else min(s[1..])
}

function method max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0] else if s[0] > max(s[1..]) then s[0] else max(s[1..])
}