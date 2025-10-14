// Dafny Code

method FindElementAfterRotations(arr: array<int>, n: int, k: int, index: int) returns (elem: int)
    requires arr != null
    requires 0 <= n == arr.Length
    requires 0 <= index < n
    ensures 0 <= elem
{
    // After k rotations (right), the element at index 'index' comes from index '(index - k + n) % n'
    var originalIndex := (index - k % n + n) % n;
    elem := arr[originalIndex];
}