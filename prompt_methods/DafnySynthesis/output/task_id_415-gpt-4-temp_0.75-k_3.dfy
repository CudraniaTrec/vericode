method maxProduct(arr:array<int>) returns (x:int, y:int)
  requires arr != null && arr.Length >= 2
{
    var n := arr.Length;
    // Find the two largest numbers
    var max1 := -2147483648; // int.MinValue
    var max2 := -2147483648;
    // Find the two smallest numbers
    var min1 := 2147483647; // int.MaxValue
    var min2 := 2147483647;
    var countMax := 0;
    var countMin := 0;

    // Collect max1, max2, min1, min2
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> arr[k] <= max1 || arr[k] >= min1
    {
        if arr[i] >= max1 {
            max2 := max1;
            max1 := arr[i];
        } else if arr[i] > max2 {
            max2 := arr[i];
        }
        if arr[i] <= min1 {
            min2 := min1;
            min1 := arr[i];
        } else if arr[i] < min2 {
            min2 := arr[i];
        }
        i := i + 1;
    }
    // Compute both products
    var prodMax := max1 * max2;
    var prodMin := min1 * min2;

    if prodMax >= prodMin {
        x := if max1 < max2 then max1 else max2;
        y := if max1 < max2 then max2 else max1;
    } else {
        x := if min1 < min2 then min1 else min2;
        y := if min1 < min2 then min2 else min1;
    }
}