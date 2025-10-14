// Dafny Code

method SmallestMissingNumber(a: seq<nat>) returns (missing: nat)
  ensures forall i :: 0 <= i < |a| ==> a[i] >= 0 // input is natural numbers
  ensures forall n :: 0 <= n < missing ==> n in a
  ensures missing !in a
{
  var left := 0;
  var right := |a|;

  while left < right
    invariant 0 <= left <= right <= |a|
    invariant forall i :: 0 <= i < left ==> a[i] == i
    invariant forall i :: right <= i < |a| ==> a[i] > i
  {
    var mid := left + (right - left) / 2;
    if mid < |a| && a[mid] == mid {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  missing := left;
}