
function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    reads a;
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
{
    sum := 0;
    var i := start;
    while i < end
        invariant start <= i <= end
        invariant sum == sumTo(a, start, i)
    {
        sum := sum + a[i];
        i := i + 1;
    }
    assert i == end;
    assert sum == sumTo(a, start, end);
}

function abs(a: real) : real {if a>0.0 then a else -a}
