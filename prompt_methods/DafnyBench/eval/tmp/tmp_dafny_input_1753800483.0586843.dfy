
predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var evenList: seq<int> := [];
    ghost var indices: seq<int> := [];

    // Loop to collect even numbers and their indices
    var i: int := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant |evenList| == |indices|
      invariant forall j :: 0 <= j < |evenList| ==> IsEven(evenList[j])
      invariant forall j :: 0 <= j < |evenList| ==> 0 <= indices[j] < i && evenList[j] == arr[indices[j]]
      invariant forall k, l :: 0 <= k < l < |evenList| ==> indices[k] < indices[l]
      invariant forall x :: x in arr[..i] && IsEven(x) ==> x in evenList
      invariant forall x :: x !in arr[..i] ==> x !in evenList
    {
        if IsEven(arr[i])
        {
          evenList := evenList + [arr[i]];
          indices := indices + [i];
        }
        i := i + 1;
    }

    evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
