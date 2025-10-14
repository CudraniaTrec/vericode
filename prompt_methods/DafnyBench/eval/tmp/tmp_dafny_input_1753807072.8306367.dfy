method remove_element(nums: array<int>, val: int) returns (i: int)
    modifies nums
    requires 0 <= nums.Length <= 100
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
    requires 0 <= val <= 100
    ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
{
    i := 0;
    var end := nums.Length - 1;

    while i <= end 
        invariant 0 <= i <= nums.Length
        invariant -1 <= end < nums.Length
        invariant i - 1 <= end + 1
        invariant forall j :: 0 <= j < i ==> nums[j] != val
        invariant forall j :: end+1 <= j < nums.Length ==> nums[j] == val
    {
        if (nums[i] == val)
        {
            if (nums[end] == val)
            {
                end := end - 1;
            }
            else {
                // nums[i] == val, nums[end] != val
                nums[i] := nums[end];
                // Now nums[i] != val
                i := i + 1;
                end := end  - 1;
            }
        }
        else {
            i := i + 1;
        }
    }
    assert forall j :: 0 <= j < i ==> nums[j] != val;
}
function abs(a: real) : real {if a>0.0 then a else -a}
