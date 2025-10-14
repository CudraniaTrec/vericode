method DifferenceFirstEvenOdd(arr: array<int>) returns (diff: int)
    requires arr != null && arr.Length > 0
    ensures -2147483648 <= diff <= 2147483647 // within int range
{
    var firstEvenFound := false;
    var firstOddFound := false;
    var firstEven := 0;
    var firstOdd := 0;

    var i := 0;
    while i < arr.Length && !(firstEvenFound && firstOddFound)
        invariant 0 <= i <= arr.Length
        invariant (firstEvenFound ==> exists j :: 0 <= j < i && arr[j] % 2 == 0)
        invariant (firstOddFound ==> exists j :: 0 <= j < i && arr[j] % 2 != 0)
    {
        if !firstEvenFound && arr[i] % 2 == 0 {
            firstEven := arr[i];
            firstEvenFound := true;
        }
        if !firstOddFound && arr[i] % 2 != 0 {
            firstOdd := arr[i];
            firstOddFound := true;
        }
        i := i + 1;
    }

    if firstEvenFound && firstOddFound {
        diff := firstEven - firstOdd;
    } else {
        // If either is not found, let's return 0 (or could raise an error/ghost assertion depending on requirements)
        diff := 0;
    }
}