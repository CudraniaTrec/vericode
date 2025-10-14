
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
    var oldArr := arr[..];
    var oldLen := arr.Length;
    var oldArrSeq := arr[..];
    var oldArrSet := set x | x in arr[..];

    var i: int := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant oddList == [arr[j] | j := 0 .. i, IsOdd(arr[j])]
        invariant forall j :: 0 <= j < |oddList| ==> IsOdd(oddList[j]) && oddList[j] in arr[..i]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
        invariant forall j :: 0 <= j < arr.Length && IsOdd(arr[j]) && j < i ==> arr[j] in oddList
        invariant forall j :: 0 <= j < arr.Length && IsOdd(arr[j]) && j >= i ==> arr[j] !in oddList
        decreases arr.Length - i
    {
        if IsOdd(arr[i])
        {
            oddList := oddList + [arr[i]];
            assert IsOdd(arr[i]);
            assert arr[i] in arr[..];
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
