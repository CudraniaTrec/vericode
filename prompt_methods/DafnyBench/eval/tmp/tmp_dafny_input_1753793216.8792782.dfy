
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    var oldArr := arr[..];
    for i := 0 to arr.Length - 1
        invariant 0 <= i <= arr.Length
        invariant pos == -1 || (0 <= pos < i && arr[pos] == elem)
        invariant forall j :: 0 <= j < i && arr[j] == elem ==> pos >= j
        invariant forall j :: 0 <= j < i ==> arr[j] == oldArr[j]
        invariant forall j :: i <= j < arr.Length ==> arr[j] == oldArr[j]
    {
        if arr[i] == elem
        {
            pos := i;
        }
    }
    assert forall i :: 0 <= i < arr.Length ==> arr[i] == oldArr[i];
    assert pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos == arr.Length - 1 || arr[pos + 1] > elem));
}

function abs(a: real) : real {if a>0.0 then a else -a}
