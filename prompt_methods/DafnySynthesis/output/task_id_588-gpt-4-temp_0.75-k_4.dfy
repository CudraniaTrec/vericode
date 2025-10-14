method FindDifference(arr: array<int>) returns (diff: int)
    requires arr != null && arr.Length > 0
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] <= arr[FindMaxIndex(arr)]
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] >= arr[FindMinIndex(arr)]
    ensures diff == arr[FindMaxIndex(arr)] - arr[FindMinIndex(arr)]
{
    var min := arr[0];
    var max := arr[0];
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> min <= arr[j] <= max
        invariant min <= max
        decreases arr.Length - i
    {
        if arr[i] < min {
            min := arr[i];
        }
        if arr[i] > max {
            max := arr[i];
        }
        i := i + 1;
    }
    diff := max - min;
}

// Helper methods to satisfy the ensures clauses
function FindMaxIndex(arr: array<int>): int
    requires arr != null && arr.Length > 0
    ensures 0 <= FindMaxIndex(arr) < arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] <= arr[FindMaxIndex(arr)]
{
    var maxIdx := 0;
    var i := 1;
    while i < arr.Length
        decreases arr.Length - i
    {
        if arr[i] > arr[maxIdx] {
            maxIdx := i;
        }
        i := i + 1;
    }
    maxIdx
}

function FindMinIndex(arr: array<int>): int
    requires arr != null && arr.Length > 0
    ensures 0 <= FindMinIndex(arr) < arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] >= arr[FindMinIndex(arr)]
{
    var minIdx := 0;
    var i := 1;
    while i < arr.Length
        decreases arr.Length - i
    {
        if arr[i] < arr[minIdx] {
            minIdx := i;
        }
        i := i + 1;
    }
    minIdx
}