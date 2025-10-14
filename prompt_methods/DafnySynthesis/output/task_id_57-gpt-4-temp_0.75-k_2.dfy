// Dafny Code

method LargestNumber(arr: array<int>) returns (result: string)
    requires arr != null
    ensures result != null
{
    var n := arr.Length;
    var strArr := new array<string>(n);
    // Convert all integers to strings
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> strArr[j] == arr[j].ToString()
    {
        strArr[i] := arr[i].ToString();
        i := i + 1;
    }

    // Custom comparator: order strings x, y so that x+y >= y+x
    // Simple Bubble Sort (since Dafny has no built-in sort)
    var swapped := true;
    while swapped
        decreases n
    {
        swapped := false;
        var j := 0;
        while j < n - 1
            invariant 0 <= j <= n-1
        {
            var xy := strArr[j] + strArr[j+1];
            var yx := strArr[j+1] + strArr[j];
            if xy < yx {
                // swap
                var tmp := strArr[j];
                strArr[j] := strArr[j+1];
                strArr[j+1] := tmp;
                swapped := true;
            }
            j := j + 1;
        }
    }

    // If the largest number is '0', return "0" (e.g., [0,0])
    if strArr[0] == "0" {
        result := "0";
        return;
    }

    // Concatenate the result
    result := "";
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result == (var z := 0; var s := ""; while z < i { s := s + strArr[z]; z := z + 1; } s)
    {
        result := result + strArr[i];
        i := i + 1;
    }
}