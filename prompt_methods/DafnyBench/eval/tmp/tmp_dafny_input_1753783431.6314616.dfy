
method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j:nat :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures  arr[index1][index2] == val
{
  // Strongest possible assertion: all arrays except arr[index1] are unchanged
  assert forall i: nat :: 0 <= i < arr.Length && i != index1 ==> arr[i] == old(arr[i]);
  // Strongest possible assertion: all elements of arr[index1] except index2 are unchanged
  assert forall j: nat :: 0 <= j < arr[index1].Length && j != index2 ==> arr[index1][j] == old(arr[index1][j]);
  arr[index1][index2] := val;
  // Strongest possible assertion: arr[index1][index2] is updated
  assert arr[index1][index2] == val;
}

function abs(a: real) : real {if a>0.0 then a else -a}
