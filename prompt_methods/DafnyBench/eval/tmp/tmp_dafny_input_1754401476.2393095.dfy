// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant m == map j | 0 <= j < i :: target - nums[j] := j
    invariant forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target
  {
    if nums[i] in m {
      // m[nums[i]] is the index j such that nums[j] == target - nums[i], 0 <= j < i
      var j := m[nums[i]];
      assert 0 <= j < i;
      assert nums[j] + nums[i] == target;
      assert forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target;
      return (j, i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  assert forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target;
  return (-1, -1);
}

function abs(a: real) : real {if a>0.0 then a else -a}
