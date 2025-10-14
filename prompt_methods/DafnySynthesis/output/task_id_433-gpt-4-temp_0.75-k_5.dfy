method IsGreaterThanAll(arr: array<int>, x: int) returns (result: bool)
    requires arr != null
    ensures result == forall i :: 0 <= i < arr.Length ==> x > arr[i]
{
    var ok := true;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant ok ==> forall j :: 0 <= j < i ==> x > arr[j]
    {
        if x <= arr[i] {
            ok := false;
            break;
        }
        i := i + 1;
    }
    return ok;
}