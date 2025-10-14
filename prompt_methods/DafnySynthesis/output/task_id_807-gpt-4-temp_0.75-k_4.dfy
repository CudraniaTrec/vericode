// Dafny Code

method FindFirstOdd(arr: array<int>) returns (index: int)
    requires arr != null
    ensures 0 <= index < arr.Length ==> arr[index] % 2 != 0
    ensures index == arr.Length || arr[index] % 2 != 0
    ensures forall k :: 0 <= k < index ==> arr[k] % 2 == 0
{
    var i := 0;
    while i < arr.Length && arr[i] % 2 == 0
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> arr[k] % 2 == 0
    {
        i := i + 1;
    }
    return i;
}