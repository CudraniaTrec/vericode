method replace(arr: array<int>, k: int)
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
{
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> old(arr[j]) > k ==> arr[j] == -1
    invariant forall j :: 0 <= j < i ==> old(arr[j]) <= k ==> arr[j] == old(arr[j])
    invariant forall j :: i <= j < arr.Length ==> arr[j] == old(arr[j])
  {
    if arr[i] > k {
      arr[i] := -1;
      assert old(arr[i]) > k;
    } else {
      assert arr[i] == old(arr[i]);
    }
    i := i + 1;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
