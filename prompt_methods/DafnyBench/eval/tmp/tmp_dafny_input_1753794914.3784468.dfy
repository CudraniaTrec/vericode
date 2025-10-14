
method binarySearch(a:array<int>, val:int) returns (pos:int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures 0 <= pos < a.Length ==> a[pos] == val
  ensures pos < 0 || pos >= a.Length  ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{
  var left := 0;
  var right := a.Length;
  if a[left] > val || a[right-1] < val 
  {
    return -1;
  }
  while left < right
    invariant 0 <= left <= right <= a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < val
    invariant forall i :: right <= i < a.Length ==> a[i] > val
    invariant right - left >= 0
  {
    var med := (left + right) / 2;
    assert left <= med < right;
    if a[med] < val
    {
      left := med + 1;
    }
    else if a[med] > val
    {
      right := med;
    }
    else
    {
      pos := med;
      assert a[pos] == val;
      return;
    }

  }
  assert forall i :: 0 <= i < a.Length ==> a[i] != val;
  return -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
