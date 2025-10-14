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
        invariant forall k :: 0 <= k < length ==> 1 <= dp[k] <= k + 1
        invariant forall k :: 0 <= k < i ==>
            (exists seq: seq<int> ::
                |seq| == dp[k] &&
                seq[|seq|-1] == nums[k] &&
                forall m :: 0 <= m < |seq|-1 ==> seq[m] < seq[m+1] &&
                forall m :: 0 <= m < |seq| ==> exists idx :: 0 <= idx <= k && seq[m] == nums[idx])
        invariant max == (if i == 1 then 1 else max_seq(dp, i))
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < length ==> 1 <= dp[k] <= k + 1
            invariant forall k :: 0 <= k < i ==>
                (exists seq: seq<int> ::
                    |seq| == dp[k] &&
                    seq[|seq|-1] == nums[k] &&
                    forall m :: 0 <= m < |seq|-1 ==> seq[m] < seq[m+1] &&
                    forall m :: 0 <= m < |seq| ==> exists idx :: 0 <= idx <= k && seq[m] == nums[idx])
        {
            if (nums[j] < nums[i])
            {
                dp[i] := find_max(dp[i], dp[j] + 1);
                assert dp[i] >= 1;
            }

            j := j + 1;
        }

        max := find_max(max, dp[i]);
        i := i + 1;
    }
}

function max_seq(a: array<int>, n: int): int
    requires 1 <= n <= a.Length
{
    if n == 1 then a[0] else if a[n-1] > max_seq(a, n-1) then a[n-1] else max_seq(a, n-1)
}

// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function abs(a: real) : real {if a>0.0 then a else -a}
