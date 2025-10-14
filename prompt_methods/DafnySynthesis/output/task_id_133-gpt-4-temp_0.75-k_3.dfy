method SumOfNegatives(nums: seq<int>) returns (sum: int)
    ensures sum == (sum x | x in nums && x < 0 :: x)
{
    sum := 0;
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant sum == (sum x | 0 <= j < i && nums[j] < 0 :: nums[j])
    {
        if nums[i] < 0 {
            sum := sum + nums[i];
        }
        i := i + 1;
    }
}