method KthElement(arr: array<int>, k: int) returns (result: int)
  requires 1 <= k <= arr.Length
  ensures result == arr[k - 1]
{
  assert 1 <= k <= arr.Length;
  assert 0 <= k - 1 < arr.Length;
  result := arr[k - 1];
  assert result == arr[k - 1];
}
function abs(a: real) : real {if a>0.0 then a else -a}
