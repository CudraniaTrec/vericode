// Dafny Code

method JoinIntegers(arr: array<int>) returns (result: int)
    requires arr != null
    ensures result == JoinIntegersSpec(arr)
{
    var res := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant res == JoinIntegersPartial(arr, i)
    {
        var num := arr[i];
        // Handle 0 specially (since log10(0) is undefined)
        var numDigits := if num == 0 then 1 else if num < 0 then NumDigits(-num) + 1 else NumDigits(num);
        res := res * pow10(numDigits) + num;
        i := i + 1;
    }
    result := res;
}

// Helper function: number of digits in a (non-negative) integer
function method NumDigits(n: int): int
    requires n >= 0
    decreases n
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// Helper function: 10^d
function method pow10(d: int): int
    requires d >= 0
    decreases d
{
    if d == 0 then 1 else 10 * pow10(d - 1)
}

// Specification function for joining integers in an array
function method JoinIntegersSpec(arr: array<int>): int
    requires arr != null
{
    if arr.Length == 0 then 0
    else JoinIntegersSpecAux(arr, 0)
}

function method JoinIntegersSpecAux(arr: array<int>, idx: int): int
    requires arr != null && 0 <= idx <= arr.Length
    decreases arr.Length - idx
{
    if idx == arr.Length then 0
    else
        var num := arr[idx];
        var numDigits := if num == 0 then 1 else if num < 0 then NumDigits(-num) + 1 else NumDigits(num);
        if idx == arr.Length - 1 then num
        else num * pow10(TotalDigits(arr, idx + 1)) + JoinIntegersSpecAux(arr, idx + 1)
}

// Helper function: total number of digits from arr[start..]
function method TotalDigits(arr: array<int>, start: int): int
    requires arr != null && 0 <= start <= arr.Length
    decreases arr.Length - start
{
    if start == arr.Length then 0
    else
        var num := arr[start];
        var numDigits := if num == 0 then 1 else if num < 0 then NumDigits(-num) + 1 else NumDigits(num);
        numDigits + TotalDigits(arr, start + 1)
}

// Partial join up to index i
function method JoinIntegersPartial(arr: array<int>, i: int): int
    requires arr != null && 0 <= i <= arr.Length
    decreases i
{
    if i == 0 then 0
    else
        var num := arr[i-1];
        var numDigits := if num == 0 then 1 else if num < 0 then NumDigits(-num) + 1 else NumDigits(num);
        JoinIntegersPartial(arr, i-1) * pow10(numDigits) + num
}