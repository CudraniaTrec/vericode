
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  var i: int := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant evenList == [arr[j] | j : int, 0 <= j < i && arr[j] % 2 == 0]
    invariant indices == [j | j : int, 0 <= j < i && arr[j] % 2 == 0]
    invariant |evenList| == |indices|
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] == arr[indices[k]]
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] % 2 == 0
    invariant forall x :: x in evenList ==> x % 2 == 0 && x in arr[..i]
    invariant forall x :: x in arr[..i] && x % 2 == 0 ==> x in evenList
    invariant forall x :: x !in arr[..i] ==> x !in evenList
  {
    if arr[i]%2==0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
      assert arr[i] % 2 == 0;
    }
    i := i + 1;
  }

  evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
  assert forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0;
  assert forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..];
  assert forall x :: x !in arr[..] ==> x !in evenNumbers[..];
  assert forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m];
}

function abs(a: real) : real {if a>0.0 then a else -a}
