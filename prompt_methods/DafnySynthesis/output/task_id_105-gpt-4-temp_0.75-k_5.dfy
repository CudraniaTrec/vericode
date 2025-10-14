method CountTrues(arr: array<bool>) returns (count: nat)
    ensures 0 <= count <= arr.Length
    ensures count == |set i | 0 <= i < arr.Length && arr[i]|
{
    count := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && arr[j]|
    {
        if arr[i] {
            count := count + 1;
        }
        i := i + 1;
    }
}