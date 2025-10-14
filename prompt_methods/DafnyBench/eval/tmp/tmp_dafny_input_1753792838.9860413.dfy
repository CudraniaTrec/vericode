
predicate IsEven(n: int)
{
    n % 2 == 0
}

method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{
    evenList := [];
    var j := 0;
    while j < arr.Length
        invariant 0 <= j <= arr.Length
        invariant evenList == [arr[k] | k :: 0 <= k < j && IsEven(arr[k])]
        invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k]) && evenList[k] in arr[..j]
        invariant forall k :: 0 <= k < j && IsEven(arr[k]) ==> arr[k] in evenList
    {
        if IsEven(arr[j])
        {
            evenList := evenList + [arr[j]];
            assert IsEven(arr[j]);
            assert arr[j] in arr[..j+1];
        }
        j := j + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
