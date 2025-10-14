/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{
    negativeList := [];
    var n := arr.Length;
    // Invariant: negativeList contains exactly all negative numbers from arr[..i]
    // Invariant: All elements in negativeList are negative and appear in arr[..i]
    // Invariant: For all j < i, if arr[j] is negative, then arr[j] is in negativeList
    // Invariant: 0 <= i <= n
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant negativeList == [arr[j] | j := 0 .. i, IsNegative(arr[j])]
        invariant forall x :: x in negativeList ==> IsNegative(x) && x in arr[..i]
        invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in negativeList
    {
        if IsNegative(arr[i])
        {
            assert arr[i] in arr[..i+1];
            negativeList := negativeList + [arr[i]];
            assert IsNegative(arr[i]);
        }
        i := i + 1;
    }
    // At this point, negativeList == [arr[j] | j := 0 .. n, IsNegative(arr[j])]
}
function abs(a: real) : real {if a>0.0 then a else -a}
