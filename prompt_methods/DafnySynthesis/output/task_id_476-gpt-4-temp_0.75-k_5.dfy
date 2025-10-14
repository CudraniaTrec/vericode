//Dafny Code

method SumOfMinAndMax(arr: array<int>) returns (sum: int)
    requires arr != null && arr.Length > 0
    ensures exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && sum == arr[i] + arr[j] &&
                        (forall k :: 0 <= k < arr.Length ==> arr[i] <= arr[k] && arr[j] >= arr[k])
{
    var min := arr[0];
    var max := arr[0];
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant min == (if forall k :: 0 <= k < i ==> arr[k] >= min then min else min)
        invariant max == (if forall k :: 0 <= k < i ==> arr[k] <= max then max else max)
        invariant forall k :: 0 <= k < i ==> min <= arr[k] <= max
    {
        if arr[i] < min {
            min := arr[i];
        }
        if arr[i] > max {
            max := arr[i];
        }
        i := i + 1;
    }
    sum := min + max;
}