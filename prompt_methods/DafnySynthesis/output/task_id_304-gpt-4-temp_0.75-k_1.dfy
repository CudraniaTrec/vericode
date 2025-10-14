// Dafny Code

method ElementAfterRotations(arr: array<int>, n: int, k: int, idx: int) returns (res: int)
  requires arr != null
  requires n == arr.Length
  requires 0 <= k
  requires 0 <= idx < n
  ensures 0 <= res < 2147483647 // result is an int
{
    // After k rotations to the right, the element at index idx 
    // comes from index (idx - k + n) % n in the original array.
    var origIdx := (idx - k + n) % n;
    res := arr[origIdx];
}