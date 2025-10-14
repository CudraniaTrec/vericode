
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    index := -1;
    var found := false;
    var breakEarly := false;
    var oldArr := arr[..];
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant index == -1 || (0 <= index < i && arr[index] == target)
        invariant forall j :: 0 <= j < i ==> arr[j] != target
        invariant !found ==> index == -1
        invariant found ==> index != -1 && arr[index] == target && index < i
        invariant breakEarly ==> forall k :: i <= k < arr.Length ==> arr[k] > target
        invariant forall k :: 0 <= k < arr.Length ==> arr[k] == oldArr[k]
    {
        if arr[i] == target
        {
            index := i;
            found := true;
            break;
        }
        if arr[i] > target
        {
            breakEarly := true;
            break;
        }
    }
    assert (index == -1) ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target;
    assert (0 <= index < arr.Length) ==> arr[index] == target;
    assert forall i :: 0 <= i < arr.Length ==> arr[i] == oldArr[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
