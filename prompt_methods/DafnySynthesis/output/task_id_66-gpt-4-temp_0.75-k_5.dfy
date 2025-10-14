method CountPositive(arr: array<int>) returns (count: int)
    ensures 0 <= count <= arr.Length
    ensures count == |set i | 0 <= i < arr.Length && arr[i] > 0|
{
    count := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && arr[j] > 0|
    {
        if arr[i] > 0 {
            count := count + 1;
        }
        i := i + 1;
    }
}