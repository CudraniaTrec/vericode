method FindFirstOdd(arr: array<int>) returns (idx: int)
    requires arr != null
    ensures 0 <= idx < arr.Length ==> arr[idx] % 2 != 0
    ensures (exists i :: 0 <= i < arr.Length && arr[i] % 2 != 0) <==> (0 <= idx < arr.Length)
    ensures forall i :: 0 <= i < idx ==> arr[i] % 2 == 0
{
    idx := 0;
    while idx < arr.Length && arr[idx] % 2 == 0
        invariant 0 <= idx <= arr.Length
        invariant forall i :: 0 <= i < idx ==> arr[i] % 2 == 0
    {
        idx := idx + 1;
    }
    // If idx == arr.Length, no odd number was found
}