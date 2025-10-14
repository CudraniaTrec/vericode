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
    // Invariant: oddList contains exactly the odd numbers from arr[0..i)
    // Invariant: All elements in oddList are odd and appear in arr[0..i)
    // Invariant: All odd numbers in arr[0..i) are in oddList
    var i: int := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant oddList == [arr[j] | j := 0 .. i, IsOdd(arr[j])]
        invariant forall x :: x in oddList ==> IsOdd(x) && x in arr[..i]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
    {
        if IsOdd(arr[i])
        {
            oddList := oddList + [arr[i]];
            assert IsOdd(arr[i]);
            assert arr[i] in arr[..i+1];
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
