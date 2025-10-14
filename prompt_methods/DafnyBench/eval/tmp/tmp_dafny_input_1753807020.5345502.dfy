
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
{
    var row := intervals.Length0;
    if (row == 0)
    {
        return 0;
    }

    bubble_sort(intervals);

    var i := 1;
    count := 1;
    var end := intervals[0, 1];
    // Invariant: 1 <= i <= row
    // Invariant: count == number of non-overlapping intervals among intervals[0..i-1] (sorted by end)
    // Invariant: forall k: int :: 1 <= k < i ==> intervals[k, 0] >= end at the time when count was incremented for k
    // Invariant: 0 <= count <= i
    // Invariant: end == the end value of the last selected non-overlapping interval among intervals[0..i-1]
    while (i < row)
        invariant 1 <= i <= row
        invariant 1 <= count <= i
        invariant end == intervals[select_last(intervals, i, count), 1]
        invariant forall k: int :: 1 <= k < i && intervals[k, 0] >= old_end(intervals, k, count, i) ==> 
            intervals[k, 0] >= old_end(intervals, k, count, i)
        decreases row - i
    {
        if (intervals[i, 0] >= end)
        {
            count := count + 1;
            end := intervals[i, 1];
            assert count <= i + 1;
        }

        i := i + 1;
    }

    assert row - count >= 0;
    return row - count;
}

// Helper function to get the index of the last selected interval
function select_last(a: array2<int>, i: int, count: int): int
    requires 1 <= i <= a.Length0
    requires 1 <= count <= i
    ensures 0 <= select_last(a, i, count) < i
{
    var idx := 0;
    var c := 1;
    var end := a[0, 1];
    var j := 1;
    while (j < i)
        decreases i - j
    {
        if (a[j, 0] >= end)
        {
            c := c + 1;
            end := a[j, 1];
            idx := j;
        }
        j := j + 1;
    }
    idx
}

// Helper function to get the end value before the k-th interval
function old_end(a: array2<int>, k: int, count: int, i: int): int
    requires 1 <= k < i <= a.Length0
    requires 1 <= count <= i
{
    var end := a[0, 1];
    var j := 1;
    while (j < k)
        decreases k - j
    {
        if (a[j, 0] >= end)
        {
            end := a[j, 1];
        }
        j := j + 1;
    }
    end
}

// Bubble Sort
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{
    var i := a.Length0 - 1;
    while (i > 0)
        invariant 0 <= i <= a.Length0 - 1
        invariant forall k :: i < k < a.Length0 ==> a[k - 1, 1] <= a[k, 1]
        decreases i
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> a[k, 1] <= a[k + 1, 1]
            decreases i - j
        {
            if (a[j, 1] > a[j + 1, 1])
            {
                a[j, 1], a[j + 1, 1] := a[j + 1, 1], a[j, 1];
            }
            j := j + 1;
        }
        i := i -1;
    }
    assert sorted(a, 0, a.Length0 - 1);
}

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}

function abs(a: real) : real {if a>0.0 then a else -a}
