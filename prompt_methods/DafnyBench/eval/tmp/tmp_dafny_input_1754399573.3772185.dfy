
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{
  var n := nums.Length;
  i := 0;
  j := 1;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant 1 <= n
    invariant forall ii,jj:: (0 <= ii < i && ii < jj < n) ==> nums[ii] + nums[jj] != target
    invariant 0 <= j <= n
  {
    j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant 0 <= i < n - 1
      invariant forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
      invariant forall ii,jj:: (0 <= ii < i && ii < jj < n) ==> nums[ii] + nums[jj] != target
    {
      if nums[i] + nums[j] == target {
        assert 0 <= i < j < n;
        assert nums[i] + nums[j] == target;
        assert forall ii,jj:: (0 <= ii < i && ii < jj < n) ==> nums[ii] + nums[jj] != target;
        assert forall jj0:: i < jj0 < j ==> nums[i] + nums[jj0] != target;
        return;
      }
      j := j + 1;
    }

    i := i + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
