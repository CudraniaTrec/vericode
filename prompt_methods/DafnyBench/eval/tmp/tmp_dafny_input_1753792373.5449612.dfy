/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
    oddList := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant oddList == (seq j | 0 <= j < i && IsOdd(arr[j]) :: arr[j])
        invariant forall j :: 0 <= j < |oddList| ==> IsOdd(oddList[j]) && oddList[j] in arr[..i]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
        decreases arr.Length - i
    {
        if IsOdd(arr[i])
        {
            oddList := oddList + [arr[i]];
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
