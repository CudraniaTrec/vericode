// Helper function to compare arrays for equality
function arrayEquals(a: array<int>, b: array<int>): bool
  requires a != null && b != null
  reads a, b
{
  a.Length == b.Length &&
  (forall i :: 0 <= i < a.Length ==> a[i] == b[i])
}

// Method to return negative numbers from input array
method negNos(list1: array<int>) returns (res: array<int>)
  requires list1 != null
  ensures res != null &&
          (forall i :: 0 <= i < res.Length ==> res[i] < 0) &&
          (forall i :: 0 <= i < list1.Length && list1[i] < 0 ==>
            (exists j :: 0 <= j < res.Length && res[j] == list1[i])) &&
          (forall j :: 0 <= j < res.Length ==>
            (exists i :: 0 <= i < list1.Length && res[j] == list1[i] && res[j] < 0))
{
  // First, count the number of negative numbers
  var count := 0;
  var i := 0;
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant 0 <= count <= i
    invariant count == (|seq j | 0 <= j < i && list1[j] < 0|)
  {
    if list1[i] < 0 {
      count := count + 1;
    }
    i := i + 1;
  }

  // Allocate result array
  res := new int[count];

  // Fill result array with negative numbers in order
  var idx := 0;
  i := 0;
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant 0 <= idx <= count
    invariant forall k :: 0 <= k < idx ==> res[k] < 0
    invariant forall k :: 0 <= k < idx ==> (exists j :: 0 <= j < i && list1[j] == res[k] && res[k] < 0)
    invariant forall j :: 0 <= j < i && list1[j] < 0 ==>
                (exists k :: 0 <= k < idx && res[k] == list1[j])
  {
    if list1[i] < 0 {
      res[idx] := list1[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
}