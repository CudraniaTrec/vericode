
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
    ensures max >= 1
{
    var length := nums.Length;
    if (length == 1)
    {
        return 1;
    }

    max := 1;
    var dp := new int[length](_ => 1);

    var i := 1;
    while (i < length)
        modifies dp
        invariant 1 <= i <= length
        invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k + 1
        invariant max == (if i == 1 then 1 else (max k :: 0 <= k < i :: dp[k]))
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> dp[i] >= dp[k] + 1 || nums[k] >= nums[i]
            invariant 1 <= dp[i] <= i + 1
        {
            if (nums[j] < nums[i])
            {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }

            j := j + 1;
        }

        max := find_max(max, dp[i]);
        i := i + 1;
    }
}


// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function abs(a: real) : real {if a>0.0 then a else -a}
