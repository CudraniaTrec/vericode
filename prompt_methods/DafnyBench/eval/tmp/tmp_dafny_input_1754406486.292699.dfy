method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
    var minVal := a[0];
    var maxVal := a[0];

    // Loop invariants: minVal and maxVal track min and max of a[0..i)
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] <= maxVal
        invariant exists k :: 0 <= k < i && minVal == a[k]
        invariant exists k :: 0 <= k < i && maxVal == a[k]
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }

    // After the loop, minVal and maxVal are the min and max of the whole array
    assert forall k :: 0 <= k < a.Length ==> minVal <= a[k] <= maxVal;
    assert exists k :: 0 <= k < a.Length && minVal == a[k];
    assert exists k :: 0 <= k < a.Length && maxVal == a[k];

    diff := maxVal - minVal;

    // Assert the postcondition
    assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff;
}

function abs(a: real) : real {if a>0.0 then a else -a}
