
predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
   var low, high := 0, a.Length;
   while low < high
         invariant 0 <= low <= high <= a.Length
         invariant forall i :: 0 <= i < low ==> a[i] < value
         invariant forall i :: high <= i < a.Length ==> a[i] > value
         invariant sorted(a)
         decreases high - low
   {
      var mid := (low + high) / 2;
      assert 0 <= mid < a.Length || (a.Length == 0 && mid == 0);
      if a[mid] < value
      {
         low := mid + 1;
      }
      else if value < a[mid]
      {
         high := mid;
      }
      else
      {
         assert low <= mid < high;
         return mid;
      }
   }
   assert forall k :: 0 <= k < a.Length ==> a[k] != value;
   return -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
