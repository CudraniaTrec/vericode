method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    var i := 1;
    // Invariants:
    //   1 <= i <= a.Length
    //   minVal == Min(a[..i])
    //   maxVal == Max(a[..i])
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        if a[i] < minVal {
            minVal := a[i];
            // minVal == Min(a[..i+1]) because a[i] < minVal == Min(a[..i])
            // So a[i] is the new minimum
        } else {
            // minVal remains the same
        }
        if a[i] > maxVal {
            maxVal := a[i];
            // maxVal == Max(a[..i+1]) because a[i] > maxVal == Max(a[..i])
            // So a[i] is the new maximum
        } else {
            // maxVal remains the same
        }
        i := i + 1;
    }
    assert minVal == Min(a[..a.Length]);
    assert maxVal == Max(a[..a.Length]);
    diff := maxVal - minVal;
}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var minPrefix := Min(a[..|a|-1]);
      if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var maxPrefix := Max(a[..|a|-1]);
      if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}

function abs(a: real) : real {if a>0.0 then a else -a}
