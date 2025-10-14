method swap(arr: array<int>, i: int, j: int)
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
{
  // arr[i] and arr[j] will be swapped, all others unchanged
  assert arr[i] == old(arr[i]);
  assert arr[j] == old(arr[j]);
  var tmp := arr[i];
  arr[i] := arr[j];
  assert arr[i] == old(arr[j]);
  arr[j] := tmp;
  assert arr[j] == old(arr[i]);
  assert forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
