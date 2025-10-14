
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  var old_evenList: seq<int>;
  var old_indices: seq<int>;

  // Loop invariant annotations
  // - evenList contains exactly the even numbers from arr[0..i)
  // - indices contains the positions of those even numbers
  // - evenList and indices have the same length
  // - for all k: 0 <= k < |evenList|, evenList[k] == arr[indices[k]]
  // - for all k: 0 <= k < |evenList|, evenList[k] % 2 == 0
  // - for all j: 0 <= j < i, if arr[j] % 2 == 0 then arr[j] in evenList
  // - for all j: 0 <= j < i, if arr[j] % 2 != 0 then arr[j] !in evenList
  // - indices is strictly increasing

  // Loop invariants
  // Strongest possible
  // (Note: triggers added for quantifiers as needed)
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant |evenList| == |indices|
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] == arr[indices[k]]
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] % 2 == 0
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in evenList
    invariant forall j :: 0 <= j < i && arr[j] % 2 != 0 ==> arr[j] !in evenList
    invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < i
    invariant forall k, l :: 0 <= k < l < |indices| ==> indices[k] < indices[l]
    invariant forall x :: x in evenList ==> exists j :: 0 <= j < i && arr[j] == x && arr[j] % 2 == 0
    invariant forall x :: x !in evenList ==> forall j :: 0 <= j < i && arr[j] == x ==> arr[j] % 2 != 0
  {
    if arr[i]%2==0
    {
      old_evenList := evenList;
      old_indices := indices;
      evenList := evenList + [arr[i]];
      indices := indices + [i];
      assert |evenList| == |old_evenList| + 1;
      assert |indices| == |old_indices| + 1;
      assert evenList[|evenList|-1] == arr[i];
      assert indices[|indices|-1] == i;
      assert evenList[|evenList|-1] % 2 == 0;
      assert forall k :: 0 <= k < |old_evenList| ==> evenList[k] == old_evenList[k];
      assert forall k :: 0 <= k < |old_indices| ==> indices[k] == old_indices[k];
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
