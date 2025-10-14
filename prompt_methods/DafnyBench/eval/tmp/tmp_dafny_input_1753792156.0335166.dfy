/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
    oddList := [];
    var j := 0;
    while j < arr.Length
        invariant 0 <= j <= arr.Length
        invariant oddList == [arr[k] | k := 0 .. j, IsOdd(arr[k])]
        invariant forall x :: x in oddList ==> IsOdd(x) && x in arr[..j]
        invariant forall k :: 0 <= k < j && IsOdd(arr[k]) ==> arr[k] in oddList
    {
        if IsOdd(arr[j])
        {
            oddList := oddList + [arr[j]];
        }
        j := j + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
