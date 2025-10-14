//Dafny Code

method SumOfNegatives(nums: seq<int>) returns (sum: int)
    ensures sum == (sum n | n in nums && n < 0 :: n)
{
    sum := 0;
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant sum == (sum n | n in nums[..i] && n < 0 :: n)
    {
        if nums[i] < 0 {
            sum := sum + nums[i];
        }
        i := i + 1;
    }
}