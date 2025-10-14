method DiffFirstEvenOdd(arr: array<int>) returns (diff: int)
    requires arr != null && arr.Length > 0
    ensures (exists i :: 0 <= i < arr.Length && arr[i] % 2 == 0) ==> // at least 1 even
            (exists j :: 0 <= j < arr.Length && arr[j] % 2 != 0) ==> // at least 1 odd
            diff == arr[FirstIndex(arr, true)] - arr[FirstIndex(arr, false)]
    decreases arr
{
    var firstEven: int := 0;
    var firstOdd: int := 0;
    var foundEven := false;
    var foundOdd := false;

    var i := 0;
    while i < arr.Length && (!foundEven || !foundOdd)
        decreases arr.Length - i
    {
        if !foundEven && arr[i] % 2 == 0 {
            firstEven := arr[i];
            foundEven := true;
        }
        if !foundOdd && arr[i] % 2 != 0 {
            firstOdd := arr[i];
            foundOdd := true;
        }
        i := i + 1;
    }
    if foundEven && foundOdd {
        diff := firstEven - firstOdd;
    } else {
        // If either even or odd is not found, set diff to 0 (or handle as appropriate)
        diff := 0;
    }
}

// Helper function to get first index of even/odd element
function FirstIndex(arr: array<int>, even: bool): int
    requires arr != null && arr.Length > 0
    requires (even ==> exists i :: 0 <= i < arr.Length && arr[i] % 2 == 0)
    requires (!even ==> exists i :: 0 <= i < arr.Length && arr[i] % 2 != 0)
    ensures 0 <= FirstIndex(arr, even) < arr.Length
    ensures even ==> arr[FirstIndex(arr, even)] % 2 == 0
    ensures !even ==> arr[FirstIndex(arr, even)] % 2 != 0
{
    var i := 0;
    while i < arr.Length
        decreases arr.Length - i
    {
        if (even && arr[i] % 2 == 0) || (!even && arr[i] % 2 != 0) {
            return i;
        }
        i := i + 1;
    }
    return -1; // Should never reach here due to preconditions
}