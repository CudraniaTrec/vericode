method IsMonotonic(arr: array<int>) returns (result: bool)
{
    if arr.Length <= 1 {
        result := true;
        return;
    }
    var increasing := true;
    var decreasing := true;
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant increasing ==> forall j :: 1 <= j < i ==> arr[j-1] <= arr[j]
        invariant decreasing ==> forall j :: 1 <= j < i ==> arr[j-1] >= arr[j]
    {
        if arr[i] > arr[i-1] {
            decreasing := false;
        }
        if arr[i] < arr[i-1] {
            increasing := false;
        }
        i := i + 1;
    }
    result := increasing || decreasing;
}