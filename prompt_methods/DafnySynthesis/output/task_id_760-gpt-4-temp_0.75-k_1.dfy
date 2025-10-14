// Dafny Code

method OnlyOneDistinctElement(nums: seq<int>) returns (res: bool)
  ensures res <==> (|nums| == 0 || (forall i :: 0 <= i < |nums| ==> nums[i] == nums[0]))
{
  if |nums| == 0 {
    // An empty sequence has zero elements, so we consider it as having only one (no) distinct element.
    return true;
  }
  var first := nums[0];
  // Check if every element equals the first one
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall j :: 0 <= j < i ==> nums[j] == first
  {
    if nums[i] != first {
      return false;
    }
    i := i + 1;
  }
  return true;
}