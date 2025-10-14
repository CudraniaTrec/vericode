
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
    var minVal := a[0];
    var maxVal := a[0];

    // Loop invariant: minVal is the minimum of a[0..i-1], maxVal is the maximum of a[0..i-1]
    // 0 <= i <= a.Length
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] <= maxVal
        invariant minVal == (if i == 1 then a[0] else (min a[j] | 0 <= j < i))
        invariant maxVal == (if i == 1 then a[0] else (max a[j] | 0 <= j < i))
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
        // Assert that minVal and maxVal are still correct
        assert forall k :: 0 <= k <= i ==> minVal <= a[k] <= maxVal;
    }
    // After the loop, minVal and maxVal are the min and max of the whole array
    assert minVal == (min a[j] | 0 <= j < a.Length);
    assert maxVal == (max a[j] | 0 <= j < a.Length);

    diff := maxVal - minVal;

    // Assert the postcondition
    assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff;
}

function abs(a: real) : real {if a>0.0 then a else -a}
