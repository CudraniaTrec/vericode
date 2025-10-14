method FilterOdds(nums: seq<int>) returns (odds: seq<int>)
    ensures odds == [x | x in nums, x % 2 != 0]
{
    var res := [];
    for x in nums {
        if x % 2 != 0 {
            res := res + [x];
        }
    }
    odds := res;
}