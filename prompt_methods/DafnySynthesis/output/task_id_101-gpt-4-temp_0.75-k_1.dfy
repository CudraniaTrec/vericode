method FindKthElement(arr: array<int>, k: int) returns (elem: int)
    requires arr != null
    requires 1 <= k <= arr.Length
    ensures elem == arr[k - 1]
{
    elem := arr[k - 1];
}