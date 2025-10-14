// Dafny Code

method RemoveOdds(arr: array<int>) returns (result: array<int>)
  ensures result != null
  ensures forall i :: 0 <= i < result.Length ==> result[i] % 2 == 0
  ensures multiset(result[..]) <= multiset(arr[..])
{
  var evenCount := 0;
  // First pass: count even numbers
  for i := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant 0 <= evenCount <= i
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> evenCount >= 1
  {
    if arr[i] % 2 == 0 {
      evenCount := evenCount + 1;
    }
  }

  // Create result array of the appropriate size
  result := new int[evenCount];
  var idx := 0;
  // Second pass: copy even numbers
  for i := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= evenCount
    invariant forall j :: 0 <= j < idx ==> result[j] % 2 == 0
    invariant forall j :: 0 <= j < idx ==> result[j] in arr[..]
  {
    if arr[i] % 2 == 0 {
      result[idx] := arr[i];
      idx := idx + 1;
    }
  }
}