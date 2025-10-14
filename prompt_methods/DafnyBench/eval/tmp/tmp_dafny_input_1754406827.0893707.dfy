method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    var i: int := 1;
    while i < a.Length
        invariant 1 <= a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
        invariant forall j :: 0 <= j < i ==> minVal <= a[j] <= maxVal
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
        i := i + 1;
    }
    assert minVal == Min(a[..a.Length]);
    assert maxVal == Max(a[..a.Length]);
    sum := minVal + maxVal;
}

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}
function abs(a: real) : real {if a>0.0 then a else -a}
