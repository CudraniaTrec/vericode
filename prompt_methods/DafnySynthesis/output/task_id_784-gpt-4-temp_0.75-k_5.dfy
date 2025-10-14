method ProductOfFirstEvenAndOdd(nums: seq<int>) returns (product: int)
    requires |nums| > 0
    ensures (exists i, j :: 0 <= i < |nums| && 0 <= j < |nums| && nums[i] % 2 == 0 && nums[j] % 2 != 0) ==> product == (nums[FirstEvenIndex(nums)] * nums[FirstOddIndex(nums)])
    ensures !(exists i :: 0 <= i < |nums| && nums[i] % 2 == 0) || !(exists j :: 0 <= j < |nums| && nums[j] % 2 != 0) ==> product == 0
{
    var firstEven := -1;
    var firstOdd := -1;

    var i := 0;
    while i < |nums| && (firstEven < 0 || firstOdd < 0)
        invariant 0 <= i <= |nums|
        invariant firstEven == -1 || 0 <= firstEven < i
        invariant firstOdd == -1 || 0 <= firstOdd < i
    {
        if firstEven == -1 && nums[i] % 2 == 0 {
            firstEven := i;
        }
        if firstOdd == -1 && nums[i] % 2 != 0 {
            firstOdd := i;
        }
        i := i + 1;
    }

    if firstEven != -1 && firstOdd != -1 {
        product := nums[firstEven] * nums[firstOdd];
    } else {
        product := 0; // If either even or odd not found
    }
}

/// Helper functions to get indices of first even/odd (for ensures)
function FirstEvenIndex(nums: seq<int>): int
    requires exists i :: 0 <= i < |nums| && nums[i] % 2 == 0
{
    var i :| 0 <= i < |nums| && nums[i] % 2 == 0;
    i
}

function FirstOddIndex(nums: seq<int>): int
    requires exists i :: 0 <= i < |nums| && nums[i] % 2 != 0
{
    var i :| 0 <= i < |nums| && nums[i] % 2 != 0;
    i
}