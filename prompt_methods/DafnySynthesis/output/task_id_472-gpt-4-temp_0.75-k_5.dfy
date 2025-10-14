//Dafny Code

method ContainsConsecutive(arr: array<int>) returns (res: bool)
    requires arr != null
    ensures res <==> (arr.Length == 0 || exists i: int, j: int :: 0 <= i < j < arr.Length && (forall k: int :: 0 <= k < arr.Length ==> arr[k] in set arr[..]) && (set arr[..]) == set s | s in arr[..] && s >= min(arr[..]) && s <= max(arr[..]) && |arr[..]| == max(arr[..]) - min(arr[..]) + 1))
{
    if arr.Length == 0 {
        // Empty array can be considered as containing consecutive numbers (by definition)
        return true;
    }

    var min := arr[0];
    var max := arr[0];

    // Find min and max
    var i := 1;
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant min == Min(arr[..i])
        invariant max == Max(arr[..i])
    {
        if arr[i] < min {
            min := arr[i];
        }
        if arr[i] > max {
            max := arr[i];
        }
        i := i + 1;
    }

    // Check if the number of distinct elements equals max - min + 1
    var setElems := set x | x in arr[..];
    if |setElems| != max - min + 1 {
        return false;
    }

    // Check if all elements in arr[..] are in [min, max]
    // This is implied by the above, but let's check anyway
    i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j: int :: 0 <= j < i ==> arr[j] >= min && arr[j] <= max
    {
        if arr[i] < min || arr[i] > max {
            return false;
        }
        i := i + 1;
    }

    return true;
}