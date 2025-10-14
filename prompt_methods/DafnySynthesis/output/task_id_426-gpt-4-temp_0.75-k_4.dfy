method FilterOddNumbers(nums: seq<int>) returns (odds: seq<int>)
  ensures odds == [x | x := nums, x % 2 != 0]
{
  var result := [];
  for i := 0 to |nums| - 1
    invariant 0 <= i <= |nums|
    invariant result == [x | x := nums[..i], x % 2 != 0]
  {
    if nums[i] % 2 != 0 {
      result := result + [nums[i]];
    }
  }
  odds := result;
}