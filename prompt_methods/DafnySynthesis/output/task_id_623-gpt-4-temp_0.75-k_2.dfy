method PowList(nums: seq<int>, n: nat) returns (result: seq<int>)
  ensures |result| == |nums|
  ensures forall i :: 0 <= i < |nums| ==> result[i] == nums[i] ^ n
{
  var res := [];
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == nums[j] ^ n
  {
    res := res + [nums[i] ^ n];
    i := i + 1;
  }
  result := res;
}