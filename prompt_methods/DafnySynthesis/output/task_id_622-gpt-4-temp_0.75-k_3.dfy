//Dafny Code

method MedianOfTwoSortedLists(A: seq<int>, B: seq<int>) returns (median: real)
    requires |A| == |B|
    requires |A| > 0
    requires forall i :: 0 <= i < |A| - 1 ==> A[i] <= A[i+1]
    requires forall i :: 0 <= i < |B| - 1 ==> B[i] <= B[i+1]
    ensures median == MedianOfSortedSequences(A, B)
{
    var n := |A|;
    var left := 0;
    var right := n;

    // Binary search on A to find correct partition
    while left <= right
        invariant 0 <= left <= right <= n
    {
        var i := (left + right) / 2;
        var j := n - i;

        var A_left := if i == 0 then -2147483648 else A[i-1];
        var A_right := if i == n then 2147483647 else A[i];
        var B_left := if j == 0 then -2147483648 else B[j-1];
        var B_right := if j == n then 2147483647 else B[j];

        if A_left <= B_right && B_left <= A_right {
            var maxLeft := if A_left > B_left then A_left else B_left;
            var minRight := if A_right < B_right then A_right else B_right;
            median := (maxLeft as real + minRight as real) / 2.0;
            return;
        } else if A_left > B_right {
            right := i - 1;
        } else {
            left := i + 1;
        }
    }
    // Will never reach here if input is valid
    median := 0.0;
}

// Helper function to define the median spec for two sorted sequences of same length
function MedianOfSortedSequences(a: seq<int>, b: seq<int>): real
    requires |a| == |b| && |a| > 0
    requires forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i+1]
    requires forall i :: 0 <= i < |b| - 1 ==> b[i] <= b[i+1]
{
    var merged := MergeSorted(a, b);
    (merged[|merged|/2 - 1] as real + merged[|merged|/2] as real) / 2.0
}

// Merge two sorted sequences
function MergeSorted(a: seq<int>, b: seq<int>): seq<int>
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then [a[0]] + MergeSorted(a[1..], b)
    else [b[0]] + MergeSorted(a, b[1..])
}