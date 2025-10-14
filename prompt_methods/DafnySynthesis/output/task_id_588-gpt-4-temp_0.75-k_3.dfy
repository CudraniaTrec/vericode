method FindDifferenceMaxMin(arr: array<int>) returns (diff: int)
    requires arr != null && arr.Length > 0
    ensures diff == (var max := (seq arr)[0];
                     var min := (seq arr)[0];
                     forall i :: 0 <= i < arr.Length ==> max >= (seq arr)[i] && min <= (seq arr)[i];
                     max - min)
{
    var max := arr[0];
    var min := arr[0];
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> max >= arr[j] && min <= arr[j]
        invariant max >= min
    {
        if arr[i] > max {
            max := arr[i];
        } else if arr[i] < min {
            min := arr[i];
        }
        i := i + 1;
    }
    diff := max - min;
}