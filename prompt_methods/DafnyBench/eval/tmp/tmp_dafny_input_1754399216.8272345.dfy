method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{
  var evenList: seq<int> := [];

  // Loop invariants:
  // - evenList contains exactly the even numbers from arr[0..i)
  // - for all k: 0 <= k < |evenList|, evenList[k] % 2 == 0
  // - for all j: 0 <= j < i, if arr[j] % 2 == 0 then arr[j] in evenList
  // - for all j: 0 <= j < i, if arr[j] % 2 != 0 then arr[j] !in evenList
  // - for all x in evenList, there exists j < i such that arr[j] == x and arr[j] % 2 == 0
  // - for all x, if x !in evenList, then for all j < i, arr[j] == x ==> arr[j] % 2 != 0
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] % 2 == 0
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in evenList
    invariant forall j :: 0 <= j < i && arr[j] % 2 != 0 ==> arr[j] !in evenList
    invariant forall x :: x in evenList ==> exists j :: 0 <= j < i && arr[j] == x && arr[j] % 2 == 0
    invariant forall x :: x !in evenList ==> forall j :: 0 <= j < i && arr[j] == x ==> arr[j] % 2 != 0
  {
    if arr[i]%2==0
    {
      evenList := evenList + [arr[i]];
    }
  }

  evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
  assert evenNumbers.Length == |evenList|;
  assert forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0;
  assert forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..];
  assert forall x :: x !in arr[..] ==> x !in evenNumbers[..];
  assert forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m];
}
function abs(a: real) : real {if a>0.0 then a else -a}
