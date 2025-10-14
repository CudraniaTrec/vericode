
method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target
        invariant exists a, b :: i <= a < b < nums.Length && nums[a] + nums[b] == target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall l :: i < l < j ==> nums[i] + nums[l] != target
            invariant forall k, l :: 0 <= k < i && k < l < nums.Length ==> nums[k] + nums[l] != target
            invariant exists a, b :: (i < a < b < nums.Length && nums[a] + nums[b] == target) || (a == i && j <= b < nums.Length && nums[i] + nums[b] == target)
        {
            if nums[i] + nums[j] == target
            {
                assert i != j;
                assert 0 <= i < nums.Length;
                assert 0 <= j < nums.Length;
                assert nums[i] + nums[j] == target;
                return i, j;
            } 
            j := j + 1;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
