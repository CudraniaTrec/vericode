// CoPilot function converted to dafny
method largest_sum(nums: array<int>, k: int) returns (sum: int)
    requires nums.Length > 0 
    ensures max_sum_subarray(nums, sum, 0, nums.Length)
{
    var max_sum := 0;
    var current_sum := 0;

    var i := 0;
    while (i < nums.Length)
        invariant 0 <= i <= nums.Length
        invariant current_sum >= 0
        invariant forall u, v :: 0 <= u < v <= i ==> Sum_Array(nums, u, v) <= max_sum
        invariant exists u, v :: 0 <= u < v <= i ==> max_sum == MaxSumSoFar(nums, i)
    {
        current_sum := current_sum + nums[i];
        if (current_sum > max_sum)
        {
            max_sum := current_sum;
        }
        if (current_sum < 0)
        {
            current_sum := 0;
        }
        i := i + 1;
    }
    assert forall u, v :: 0 <= u < v <= nums.Length ==> Sum_Array(nums, u, v) <= max_sum;
    sum := max_sum;
}

// Predicate to confirm that sum is the maximum summation of element [start, stop) 
predicate max_sum_subarray(arr: array<int>, sum: int, start: int, stop: int)
    requires arr.Length > 0
    requires 0 <= start <= stop <= arr.Length
    reads arr
{
    forall u, v :: start <= u < v <= stop ==> Sum_Array(arr, u, v) <= sum
}

// Helper function to compute the maximum sum of any subarray in arr[0..upto)
function MaxSumSoFar(arr: array<int>, upto: int): int
    requires 0 <= upto <= arr.Length
    reads arr
{
    if upto == 0 then 0
    else Max(MaxSumSoFar(arr, upto - 1), MaxSubarrayEndingAt(arr, upto))
}

// Maximum sum of any subarray ending at position upto
function MaxSubarrayEndingAt(arr: array<int>, upto: int): int
    requires 0 < upto <= arr.Length
    reads arr
{
    if upto == 0 then 0
    else maxSeq({ Sum_Array(arr, j, upto) | j : int, 0 <= j < upto })
}

// Maximum of a nonempty set of ints
function method Max(a: int, b: int): int
{
    if a > b then a else b
}

// Maximum of a nonempty sequence of ints
function method maxSeq(s: set<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[*] else Max(s.choose(), maxSeq(s - {s.choose()}))
}

// Sums array elements between [start, stop)
function Sum_Array(arr: array<int>, start: int, stop: int): int
    requires 0 <= start <= stop <= arr.Length
    reads arr
{
    if start >= stop then 0
    else arr[stop-1] + Sum_Array(arr, start, stop-1)
}

function abs(a: real) : real {if a>0.0 then a else -a}
