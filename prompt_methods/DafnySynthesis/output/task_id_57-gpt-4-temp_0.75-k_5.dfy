// Dafny Code

method LargestNumber(nums: seq<int>) returns (largest: string)
    requires forall n :: n in nums ==> n >= 0 // Only non-negative integers
{
    // Helper function to convert int to string
    function method itos(n: int): string
        requires n >= 0
    {
        if n == 0 then "0"
        else if n < 10 then [char]('0' + n)
        else itos(n / 10) + [char]('0' + n % 10)
    }

    // Helper function to compare two numbers by their concatenation order
    function method better(a: int, b: int): bool
        requires a >= 0 && b >= 0
        decreases a, b
    {
        itos(a) + itos(b) >= itos(b) + itos(a)
    }

    // Simple bubble sort based on the custom comparator
    var arr := nums[..];
    var n := |arr|;
    var i := 0;
    while i < n
        decreases n - i
    {
        var j := 0;
        while j < n - 1
            decreases n - 1 - j
        {
            if !better(arr[j], arr[j+1]) {
                var tmp := arr[j];
                arr[j] := arr[j+1];
                arr[j+1] := tmp;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Concatenate all numbers
    var res := "";
    var k := 0;
    while k < n
        decreases n - k
    {
        res := res + itos(arr[k]);
        k := k + 1;
    }

    // Handle the case where the largest number is 0 (all zeros)
    if res[0] == '0' {
        largest := "0";
    } else {
        largest := res;
    }
}