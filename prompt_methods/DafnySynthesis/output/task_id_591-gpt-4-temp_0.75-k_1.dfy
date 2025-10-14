method SwapFirstAndLast(arr: array<int>)
  requires arr != null && arr.Length >= 2
  modifies arr
  ensures arr[0] == old(arr[arr.Length - 1]) && arr[arr.Length - 1] == old(arr[0])
  ensures forall i :: 1 <= i < arr.Length - 1 ==> arr[i] == old(arr[i])
{
  var tmp := arr[0];
  arr[0] := arr[arr.Length - 1];
  arr[arr.Length - 1] := tmp;
}