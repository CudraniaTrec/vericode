method IsGreaterThanAll(arr: array<int>, n: int) returns (res: bool)
    requires arr != null
    ensures res <==> forall i :: 0 <= i < arr.Length ==> n > arr[i]
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> n > arr[j]
    {
        if !(n > arr[i]) {
            res := false;
            return;
        }
        i := i + 1;
    }
    res := true;
}