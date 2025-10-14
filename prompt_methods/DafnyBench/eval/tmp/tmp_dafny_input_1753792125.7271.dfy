/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{
    evenList := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant evenList == (seq j := 0 to i-1 | IsEven(arr[j]) :: arr[j])
        invariant forall x :: x in evenList ==> IsEven(x) && x in arr[..i]
        invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> arr[j] in evenList
    {
        if IsEven(arr[i])
        {
            evenList := evenList + [arr[i]];
            assert IsEven(arr[i]);
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
