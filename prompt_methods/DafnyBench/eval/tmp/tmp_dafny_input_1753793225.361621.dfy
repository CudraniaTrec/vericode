method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos == arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    var oldArr := arr[..];
    for i := 0 to arr.Length - 1
        invariant 0 <= i <= arr.Length
        invariant pos == -1 || (0 <= pos < i && arr[pos] == elem)
        invariant forall j :: 0 <= j < i && arr[j] == elem ==> pos >= j
        invariant forall j :: 0 <= j < arr.Length ==> arr[j] == oldArr[j]
    {
        if arr[i] == elem
        {
            pos := i;
        }
    }
    // At this point, either pos == -1 (elem not found), or arr[pos] == elem and for all j > pos, arr[j] != elem
    // Since arr is sorted, if arr[pos] == elem, then arr[pos+1] > elem or pos == arr.Length-1
    if pos != -1 && pos < arr.Length - 1 {
        // For all j > pos, arr[j] != elem, so arr[pos+1] != elem
        // Since arr is sorted and arr[pos] == elem, arr[pos+1] >= arr[pos]
        // So arr[pos+1] > elem
        assert forall j :: pos < j < arr.Length ==> arr[j] != elem;
        assert arr[pos+1] != elem;
        assert arr[pos+1] >= arr[pos];
        assert arr[pos] == elem;
        assert arr[pos+1] > elem;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
