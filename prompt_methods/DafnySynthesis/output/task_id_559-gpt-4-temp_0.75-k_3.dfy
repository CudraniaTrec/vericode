//Dafny Code

method MaxSubArraySum(a: array<int>) returns (maxSum: int)
    requires a != null && a.Length > 0
    ensures forall i, j :: 0 <= i <= j < a.Length ==> maxSum >= sum(a, i, j)
    ensures exists i, j :: 0 <= i <= j < a.Length && maxSum == sum(a, i, j)
{
    var currentMax := a[0];
    maxSum := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant maxSum == MaxSeqSum(a, 0, i)
        invariant currentMax == MaxEndingHere(a, i-1)
    {
        currentMax := if currentMax + a[i] > a[i] then currentMax + a[i] else a[i];
        if currentMax > maxSum {
            maxSum := currentMax;
        }
        i := i + 1;
    }
}

// Helper function: sum of a[i..j]
function sum(a: array<int>, i: int, j: int): int
    requires a != null && 0 <= i <= j < a.Length
{
    if i > j then 0 else a[i] + sum(a, i+1, j)
}

// Helper function: maximum sum of any subarray ending at endIndex
function MaxEndingHere(a: array<int>, endIndex: int): int
    requires a != null && 0 <= endIndex < a.Length
{
    if endIndex == 0 then a[0]
    else Max(a[endIndex], MaxEndingHere(a, endIndex-1) + a[endIndex])
}

// Helper function: maximum sum of any subarray in a[0..i-1]
function MaxSeqSum(a: array<int>, start: int, end_: int): int
    requires a != null && 0 <= start <= end_ <= a.Length
{
    if start == end_ then a[start-1]
    else if start == 0 then MaxEndingHere(a, end_-1)
    else Max(MaxSeqSum(a, start, end_-1), MaxEndingHere(a, end_-1))
}

// Helper function: maximum of two ints
function Max(x: int, y: int): int
{
    if x > y then x else y
}