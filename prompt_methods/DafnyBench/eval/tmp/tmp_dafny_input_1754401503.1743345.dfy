method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
    var i := 0;
    var j := 0;
    // Invariant: 0 <= i <= nums.Length
    // Invariant: 0 <= j <= i
    // Invariant: forall k :: 0 <= k < j ==> nums[k] != val
    // Invariant: multiset(nums[..j]) + multiset(nums[i..]) == multiset(old(nums[..]))
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= j <= i
        invariant forall k :: 0 <= k < j ==> nums[k] != val
        invariant multiset(nums[..j]) + multiset(nums[i..]) == multiset(old(nums[..]))
    {
        if nums[i] != val {
            nums[j] := nums[i];
            j := j + 1;
        }
        i := i + 1;
    }
    newLength := j;
    return j;
}
function abs(a: real) : real {if a>0.0 then a else -a}
