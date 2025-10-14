
method modify_array_element(arr: array<array<nat>>, index1: nat, index2: nat, val: nat)
  requires index1 < arr.Length
  requires index2 < arr[index1].Length
  requires forall i: nat, j:nat :: i < arr.Length && j < arr.Length && i != j ==> arr[i] != arr[j]
  modifies arr[index1]
  ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  ensures forall i: nat, j: nat :: 0 <= i < arr.Length && 0 <= j < arr[i].Length && (i != index1 || j != index2) ==> arr[i][j] == old(arr[i][j])
  ensures  arr[index1][index2] == val
{
  // Strongest annotation: arr[index1] is the same reference as old(arr[index1])
  assert arr[index1] == old(arr[index1]);
  // All other arr[i] are the same reference as old(arr[i])
  var n := arr.Length;
  var m := arr[index1].Length;
  // Strongest annotation: for all i != index1, arr[i] == old(arr[i])
  assert forall i: nat :: 0 <= i < n && i != index1 ==> arr[i] == old(arr[i]);
  // Strongest annotation: for all i, j != index2, arr[index1][j] == old(arr[index1][j])
  assert forall j: nat :: 0 <= j < m && j != index2 ==> arr[index1][j] == old(arr[index1][j]);
  // Strongest annotation: for all i != index1, for all j, arr[i][j] == old(arr[i][j])
  assert forall i: nat, j: nat :: 0 <= i < n && i != index1 && 0 <= j < arr[i].Length ==> arr[i][j] == old(arr[i][j]);
  arr[index1][index2] := val;
  // Strongest annotation: arr[index1][index2] == val
  assert arr[index1][index2] == val;
}

function abs(a: real) : real {if a>0.0 then a else -a}
