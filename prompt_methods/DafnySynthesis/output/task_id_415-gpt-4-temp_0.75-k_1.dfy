method FindMaxProductPair(arr: array<int>) returns (a: int, b: int)
    requires arr != null && arr.Length >= 2
    ensures exists i, j :: 0 <= i < j < arr.Length && (a == arr[i] && b == arr[j] || a == arr[j] && b == arr[i])
    ensures forall i, j :: 0 <= i < j < arr.Length ==> a * b >= arr[i] * arr[j]
{
    var max1 := if arr[0] >= arr[1] then arr[0] else arr[1];
    var max2 := if arr[0] < arr[1] then arr[0] else arr[1];
    var min1 := if arr[0] <= arr[1] then arr[0] else arr[1];
    var min2 := if arr[0] > arr[1] then arr[0] else arr[1];

    var i := 2;
    while i < arr.Length
        invariant 2 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> 
            (max1 >= arr[k] && max2 >= arr[k]) ||
            (min1 <= arr[k] && min2 <= arr[k])
    {
        if arr[i] > max1 {
            max2 := max1;
            max1 := arr[i];
        } else if arr[i] > max2 {
            max2 := arr[i];
        }
        if arr[i] < min1 {
            min2 := min1;
            min1 := arr[i];
        } else if arr[i] < min2 {
            min2 := arr[i];
        }
        i := i + 1;
    }

    if max1 * max2 >= min1 * min2 {
        a, b := max1, max2;
    } else {
        a, b := min1, min2;
    }
}